#!/usr/bin/env python3
"""Run the mandatory, fail-closed terminal gate on proposed challenge claims.

Input may be a JSON object, a JSON list, or JSONL.  Every submitted row must
pass.  The command exits nonzero for an empty input, malformed evidence, an
unsupported PBB/non-CSS claim, or any rejected candidate.
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.certificate import verify_css_certificate


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
        "--output",
        type=Path,
        default=project / "results" / "final_gate.json",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        rows = load_rows(args.claims)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"FINAL GATE FAILED: cannot load claims: {exc}", file=sys.stderr)
        return 2

    if not rows or any(
        row.get("certificate_type") != "qldpc-css-bb-exact" for row in rows
    ):
        print(
            "FINAL GATE FAILED: raw candidate metadata is forbidden; "
            "run scripts/build_certificate.py first",
            file=sys.stderr,
        )
        return 2
    evaluations = []
    for index, certificate in enumerate(rows):
        verification = verify_css_certificate(
            certificate,
            known_answer_artifact=args.known_answer_artifact,
            rerun_milp=True,
        )
        evaluations.append({
            "source_index": index,
            "claim": certificate.get("claim"),
            "certificate_sha256": certificate.get("certificate_sha256"),
            "result": verification,
        })
    accepted = sum(item["result"].get("passed") is True for item in evaluations)
    passed = bool(evaluations) and accepted == len(evaluations)
    artifact = {
        "schema_version": 1,
        "gate": "qldpc-challenge-final-batch",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "passed": passed,
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
