#!/usr/bin/env python3
"""Certify and independently verify every eligible challenge win in one run."""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.certificate_dispatch import (
    build_certificate,
    verify_certificate,
)
from evaluation.final_gate import classify_win
from evaluation.known_answer_integrity import check_known_answer_integrity
from evaluation.release_gate import canonical_sha256


def load_evaluations(path: Path) -> list[dict]:
    return [
        json.loads(line) for line in path.read_text().splitlines()
        if line.strip()
    ]


def eligible(row: dict) -> bool:
    novelty = row.get("structural_novelty") or {}
    details = row.get("milp_details") or {}
    k = int(row.get("k", 0) or 0)
    return bool(
        k > 0
        and int(row.get("d", 0) or 0) > 0
        and row.get("d_is_exact") is True
        and row.get("milp_attempted") is True
        and details.get("exact") is True
        and int(details.get("total_logicals", 0)) == 2 * k
        and int(details.get("num_logicals_checked", 0)) == 2 * k
        and int(details.get("logicals_optimal", 0)) == 2 * k
        and novelty.get("checked") is True
        and novelty.get("novel") is True
        and classify_win(
            int(row.get("n", 0)), k, int(row.get("d", 0)),
        )["passed"]
    )


def main() -> int:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--limit", type=int, default=3)
    parser.add_argument(
        "--known-answer-mode",
        choices=("strict",),
        default="strict",
        help="Formal releases require a fresh strict known-answer replay.",
    )
    parser.add_argument(
        "--known-answer-artifact", type=Path,
        default=project / "results" / "known_answer_gate.json",
    )
    parser.add_argument(
        "--known-answer-trust", type=Path,
        default=project / "results" / "known_answer_trust.json",
    )
    parser.add_argument("--timeout-per-logical", type=float, default=300)
    parser.add_argument("--total-timeout", type=float, default=7200)
    args = parser.parse_args()
    run_root = project / "results" / "runs" / args.run_id
    evaluations_path = run_root / "evaluations.jsonl"
    release_path = run_root / "challenge_manifest.json"
    certificates_dir = run_root / "certificates"

    integrity = check_known_answer_integrity(
        args.known_answer_artifact,
        args.known_answer_trust,
        mode=args.known_answer_mode,
        timeout_per_logical=int(args.timeout_per_logical),
        total_timeout_per_code=int(args.total_timeout),
    )
    rows = load_evaluations(evaluations_path)
    candidates = [row for row in rows if eligible(row)]
    candidates.sort(key=lambda row: float(row.get("fom", 0)), reverse=True)
    if args.limit:
        candidates = candidates[:args.limit]

    entries = []
    if integrity["passed"]:
        certificates_dir.mkdir(parents=True, exist_ok=True)
        for index, row in enumerate(candidates):
            certificate = build_certificate(
                row,
                known_answer_artifact=args.known_answer_artifact,
                timeout_per_logical=args.timeout_per_logical,
                total_timeout=args.total_timeout,
            )
            filename = f"candidate-{index:03d}.json"
            certificate_path = certificates_dir / filename
            temporary = certificate_path.with_suffix(".json.tmp")
            temporary.write_text(json.dumps(certificate, indent=2) + "\n")
            temporary.replace(certificate_path)
            verification = verify_certificate(
                certificate,
                known_answer_artifact=args.known_answer_artifact,
                rerun_milp=True,
                timeout_per_logical=args.timeout_per_logical,
            )
            entries.append({
                "file": f"certificates/{filename}",
                "certificate_sha256": certificate["certificate_sha256"],
                "verification": verification,
            })

    passed = bool(entries) and all(
        entry["verification"].get("passed") is True for entry in entries
    )
    manifest = {
        "schema_version": 1,
        "gate": "qldpc-challenge-release",
        "run_id": args.run_id,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "passed": passed,
        "known_answer_integrity": integrity,
        "source_evaluations": len(rows),
        "eligible_candidates": len(candidates),
        "certificates": entries,
    }
    manifest["manifest_sha256"] = canonical_sha256(
        manifest, omit="manifest_sha256",
    )
    run_root.mkdir(parents=True, exist_ok=True)
    temporary = release_path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(manifest, indent=2) + "\n")
    temporary.replace(release_path)
    print(
        f"CHALLENGE RELEASE {'PASSED' if passed else 'FAILED'}: "
        f"{sum(e['verification'].get('passed') is True for e in entries)}/"
        f"{len(entries)} certificates; manifest={release_path}"
    )
    if not integrity["passed"]:
        for failure in integrity["failures"]:
            print(f"  known-answer: {failure}")
    if not candidates:
        print("  no structurally novel, exact, winning candidates in run")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
