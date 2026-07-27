#!/usr/bin/env python3
"""Fully replay every certificate in a challenge release manifest."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.certificate_dispatch import verify_certificate
from evaluation.known_answer_integrity import check_known_answer_integrity
from evaluation.release_gate import (
    resolve_release_certificate_path,
    validate_release_manifest,
)


STRICT_PROVENANCE_FIELDS = (
    "artifact_sha256",
    "semantic_sha256",
    "rerun_semantic_sha256",
    "environment",
)


def compare_strict_provenance(recorded: dict, fresh: dict) -> list[str]:
    return [
        f"known-answer fresh strict {field} differs from release manifest"
        for field in STRICT_PROVENANCE_FIELDS
        if fresh.get(field) != recorded.get(field)
    ]


def main() -> int:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--run-id")
    parser.add_argument("--known-answer-mode", choices=("strict",), default="strict")
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
        args.manifest,
        known_answer_trust_path=args.known_answer_trust,
        expected_run_id=args.run_id,
    )
    if static.get("passed") is not True:
        failures = list(static.get("failures", []))
        print(
            "RELEASE REPLAY FAILED: "
            f"0/{static.get('certificates', 0)} certificates"
        )
        for failure in failures:
            print(f"  {failure}")
        return 1

    integrity = check_known_answer_integrity(
        args.known_answer_artifact,
        args.known_answer_trust,
        mode=args.known_answer_mode,
        timeout_per_logical=args.known_answer_timeout_per_logical,
        total_timeout_per_code=args.known_answer_total_timeout,
    )
    failures = [
        f"known-answer: {failure}" for failure in integrity.get("failures", [])
    ]
    manifest = json.loads(args.manifest.read_text())
    failures.extend(compare_strict_provenance(
        manifest["known_answer_integrity"], integrity,
    ))
    verified = 0
    if integrity.get("passed") is True and not failures:
        for index, entry in enumerate(manifest["certificates"]):
            certificate_path = resolve_release_certificate_path(
                args.manifest, entry.get("file"),
            )
            certificate = json.loads(certificate_path.read_text())
            result = verify_certificate(
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
