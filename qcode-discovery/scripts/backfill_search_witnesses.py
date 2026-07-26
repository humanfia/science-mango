#!/usr/bin/env python3
"""Replay search directions and attach self-contained packed Pauli witnesses."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.certificate import pack_vector
from evaluation.noncss_certificate import (
    solve_symplectic_direction,
    verify_symplectic_witness,
)
from evaluation.pbb_code import build_pbb_code, get_symplectic_logicals


def backfill_record(record: dict[str, Any], *, timeout: float) -> dict[str, Any]:
    claim = record["claim"]
    code = build_pbb_code(
        int(claim["ell"]), int(claim["m"]),
        claim["A_terms"], claim["B_terms"], claim["C_terms"], claim["D_terms"],
    )
    stabilizer = np.asarray(code.matrix, dtype=np.uint8) & 1
    logicals = get_symplectic_logicals(code)
    updated = dict(record)
    directions = []
    for stored in record.get("directions", []):
        index = int(stored["logical_index"])
        target = logicals[index]
        solved = solve_symplectic_direction(
            stabilizer, target, timeout=timeout,
        )
        if solved["operator"] is None or solved["objective"] is None:
            raise RuntimeError(
                f"trial {record.get('trial')} logical {index}: no feasible witness"
            )
        direction = {
            "logical_index": index,
            "objective": solved["objective"],
            "success": solved["success"],
            "status": solved["status"],
            "message": solved["message"],
            "mip_gap": solved["mip_gap"],
            "mip_dual_bound": solved["mip_dual_bound"],
            "mip_node_count": solved["mip_node_count"],
            "elapsed_s": solved["elapsed_s"],
            "operator": solved["operator"],
            "target_logical": pack_vector(target),
        }
        failures = verify_symplectic_witness(direction, stabilizer, target)
        direction["witness_verified"] = not failures
        direction["witness_failures"] = failures
        if failures:
            raise RuntimeError(
                f"trial {record.get('trial')} logical {index}: "
                + "; ".join(failures)
            )
        directions.append(direction)
    updated["directions"] = directions
    updated["distance"] = min(
        (int(item["objective"]) for item in directions),
        default=int(record.get("distance", 0)),
    )
    updated["fom"] = (
        int(updated["k"]) * updated["distance"] ** 2 / int(updated["n"])
        if updated["distance"] else 0.0
    )
    updated["witnesses_self_contained"] = all(
        item["witness_verified"] for item in directions
    )
    return updated


def rewrite_jsonl(path: Path, *, timeout: float) -> int:
    rows = [
        json.loads(line) for line in path.read_text().splitlines()
        if line.strip()
    ]
    updated = [backfill_record(row, timeout=timeout) for row in rows]
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        "".join(json.dumps(row, separators=(",", ":")) + "\n" for row in updated)
    )
    temporary.replace(path)
    return len(updated)


def refresh_summary(summary_path: Path) -> None:
    summary = json.loads(summary_path.read_text())
    for run in summary.get("runs", []):
        artifact = run.get("artifact")
        if not artifact:
            continue
        path = summary_path.parent / artifact
        run["artifact_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
    temporary = summary_path.with_suffix(summary_path.suffix + ".tmp")
    temporary.write_text(json.dumps(summary, indent=2) + "\n")
    temporary.replace(summary_path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="+", type=Path)
    parser.add_argument("--timeout-per-direction", type=float, default=60)
    parser.add_argument("--summary", type=Path)
    args = parser.parse_args()
    total = 0
    for path in args.files:
        count = rewrite_jsonl(path, timeout=args.timeout_per_direction)
        total += count
        print(f"backfilled={count} artifact={path}")
    if args.summary:
        refresh_summary(args.summary)
        print(f"summary_hashes_refreshed={args.summary}")
    print(f"total_backfilled={total}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
