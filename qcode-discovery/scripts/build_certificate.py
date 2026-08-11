#!/usr/bin/env python3
"""Build a full exact CSS BB challenge certificate from one candidate."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.certificate_dispatch import (
    EXACT_ANCHOR_CSS_TYPE,
    build_certificate,
)
from evaluation.sector_certificate import (
    STAGE3_GATE as SECTOR_SAT_STAGE3_GATE,
    claim_from_sector_sat_artifact,
)
from scripts.screen_frontier_twobga import (
    TWOBGA_STAGE3_GATE,
    claim_from_twobga_artifact,
)
from scripts.screen_frontier_candidate import (
    STAGE3_GATE,
    claim_from_threshold_artifact,
)


def _unwrap_candidate(value: dict) -> dict:
    if value.get("gate") == STAGE3_GATE:
        return claim_from_threshold_artifact(value)
    if value.get("gate") == SECTOR_SAT_STAGE3_GATE:
        return claim_from_sector_sat_artifact(value)
    if value.get("gate") == TWOBGA_STAGE3_GATE:
        return claim_from_twobga_artifact(value)
    return value


def load_one(path: Path, index: int) -> dict:
    text = path.read_text()
    try:
        value = json.loads(text)
    except json.JSONDecodeError:
        value = [json.loads(line) for line in text.splitlines() if line.strip()]
    if isinstance(value, dict):
        return _unwrap_candidate(value)
    if not isinstance(value, list) or not 0 <= index < len(value):
        raise ValueError(f"candidate index {index} is unavailable")
    if not isinstance(value[index], dict):
        raise ValueError("selected candidate is not a JSON object")
    return _unwrap_candidate(value[index])


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
    parser.add_argument("--checkpoint", type=Path)
    parser.add_argument(
        "--resume",
        action=argparse.BooleanOptionalAction,
        default=True,
    )
    parser.add_argument("--solver-workers", type=int, default=1)
    args = parser.parse_args()
    checkpoint = args.checkpoint or args.output.with_suffix(
        args.output.suffix + ".checkpoint.json",
    )
    try:
        claim = load_one(args.candidate, args.index)
        certificate = build_certificate(
            claim,
            known_answer_artifact=args.known_answer_artifact,
            timeout_per_logical=args.timeout_per_logical,
            total_timeout=args.total_timeout,
            checkpoint_path=checkpoint,
            resume=args.resume,
            solver_workers=args.solver_workers,
        )
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print(f"CERTIFICATE BUILD FAILED: {exc}", file=sys.stderr)
        return 2
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(json.dumps(certificate, indent=2) + "\n")
    temporary.replace(args.output)
    if certificate.get("certificate_type") == EXACT_ANCHOR_CSS_TYPE:
        parameters = certificate.get("parameters") or {}
        print(
            "CERTIFICATE PACKAGED (VERIFICATION REQUIRED; "
            "CALIBRATION ONLY / NOT A WIN): "
            f"n={parameters.get('n')} k={parameters.get('k')} "
            f"d={parameters.get('d')} output={args.output}"
        )
        return 0
    status = (
        "BUILT (INDEPENDENT REPLAY REQUIRED)"
        if certificate["passed"] else "NOT A CHALLENGE WIN"
    )
    if isinstance(certificate.get("twobga_exact"), dict):
        proof = certificate["twobga_exact"]
        detail = (
            f"d={proof['distance']} auxiliary_sectors="
            f"{len(proof.get('lower_bound_decisions') or [])}/2"
        )
    elif isinstance(certificate.get("sector_exact"), dict):
        proof = certificate["sector_exact"]
        detail = (
            f"d={proof['distance']} sector_decisions="
            f"{proof['completed_lower_decisions']}/"
            f"{proof['expected_lower_decisions']}"
        )
    else:
        proof = certificate["milp"]
        detail = (
            f"d={proof['distance']} directions="
            f"{proof['completed_directions']}/{proof['expected_directions']}"
        )
    print(f"CERTIFICATE {status}: {detail} output={args.output}")
    if not certificate["passed"]:
        print("; ".join(certificate["final_gate"].get("failures") or []))
    return 0 if certificate["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
