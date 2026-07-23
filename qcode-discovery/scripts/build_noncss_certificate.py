#!/usr/bin/env python3
"""Build a replayable exact certificate for a PBB or non-CSS matrix claim."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.noncss_certificate import build_noncss_certificate


def main() -> int:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("claim", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--known-answer-artifact", type=Path,
        default=project / "results" / "known_answer_gate.json",
    )
    parser.add_argument("--timeout-per-logical", type=float, default=300)
    parser.add_argument("--total-timeout", type=float, default=7200)
    args = parser.parse_args()
    certificate = build_noncss_certificate(
        json.loads(args.claim.read_text()),
        known_answer_artifact=args.known_answer_artifact,
        timeout_per_logical=args.timeout_per_logical,
        total_timeout=args.total_timeout,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(certificate, indent=2) + "\n")
    print(
        f"certificate={args.output} passed={certificate['passed']} "
        f"d={certificate['milp']['distance']}"
    )
    return 0 if certificate["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
