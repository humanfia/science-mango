#!/usr/bin/env python3
"""Build a full exact CSS BB challenge certificate from one candidate."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.certificate import build_css_certificate


def load_one(path: Path, index: int) -> dict:
    text = path.read_text()
    try:
        value = json.loads(text)
    except json.JSONDecodeError:
        value = [json.loads(line) for line in text.splitlines() if line.strip()]
    if isinstance(value, dict):
        return value
    if not isinstance(value, list) or not 0 <= index < len(value):
        raise ValueError(f"candidate index {index} is unavailable")
    if not isinstance(value[index], dict):
        raise ValueError("selected candidate is not a JSON object")
    return value[index]


def main() -> int:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--index", type=int, default=0)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--known-answer-artifact", type=Path,
        default=project / "results" / "known_answer_gate.json",
    )
    parser.add_argument("--timeout-per-logical", type=float, default=300)
    parser.add_argument("--total-timeout", type=float, default=7200)
    args = parser.parse_args()
    try:
        claim = load_one(args.candidate, args.index)
        certificate = build_css_certificate(
            claim,
            known_answer_artifact=args.known_answer_artifact,
            timeout_per_logical=args.timeout_per_logical,
            total_timeout=args.total_timeout,
        )
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print(f"CERTIFICATE BUILD FAILED: {exc}", file=sys.stderr)
        return 2
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(json.dumps(certificate, indent=2) + "\n")
    temporary.replace(args.output)
    status = "PASSED" if certificate["passed"] else "NOT A CHALLENGE WIN"
    print(
        f"CERTIFICATE {status}: d={certificate['milp']['distance']} "
        f"directions={certificate['milp']['completed_directions']}/"
        f"{certificate['milp']['expected_directions']} output={args.output}"
    )
    if not certificate["passed"]:
        print("; ".join(certificate["final_gate"].get("failures") or []))
    return 0 if certificate["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
