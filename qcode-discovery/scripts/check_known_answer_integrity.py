#!/usr/bin/env python3
"""Validate the known-answer artifact in fast pinned or strict rerun mode."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.known_answer_integrity import check_known_answer_integrity


def main() -> int:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("fast", "strict"), default="strict")
    parser.add_argument(
        "--artifact", type=Path,
        default=project / "results" / "known_answer_gate.json",
    )
    parser.add_argument(
        "--trust", type=Path,
        default=project / "results" / "known_answer_trust.json",
    )
    parser.add_argument("--timeout-per-logical", type=int, default=300)
    parser.add_argument("--total-timeout-per-code", type=int, default=7200)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        result = check_known_answer_integrity(
            args.artifact, args.trust, mode=args.mode,
            timeout_per_logical=args.timeout_per_logical,
            total_timeout_per_code=args.total_timeout_per_code,
        )
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"KNOWN-ANSWER INTEGRITY FAILED: {exc}", file=sys.stderr)
        return 2
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        temporary = args.output.with_suffix(args.output.suffix + ".tmp")
        temporary.write_text(json.dumps(result, indent=2) + "\n")
        temporary.replace(args.output)
    print(
        f"KNOWN-ANSWER {args.mode.upper()} "
        f"{'PASSED' if result['passed'] else 'FAILED'}"
    )
    for failure in result["failures"]:
        print(f"  {failure}")
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
