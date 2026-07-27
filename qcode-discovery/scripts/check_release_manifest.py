#!/usr/bin/env python3
"""Fail closed unless a challenge release manifest is immutable and verified."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.release_gate import validate_release_manifest


def main() -> int:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--run-id")
    parser.add_argument(
        "--known-answer-trust",
        type=Path,
        default=project / "results" / "known_answer_trust.json",
    )
    args = parser.parse_args()
    result = validate_release_manifest(
        args.manifest,
        known_answer_trust_path=args.known_answer_trust,
        expected_run_id=args.run_id,
    )
    print(
        f"RELEASE MANIFEST {'PASSED' if result['passed'] else 'FAILED'}: "
        f"{result.get('verified', 0)}/{result.get('certificates', 0)} verified"
    )
    for failure in result["failures"]:
        print(f"  {failure}")
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
