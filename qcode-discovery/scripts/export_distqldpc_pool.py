#!/usr/bin/env python3
"""Export unresolved CSS candidates for the external DistQLDPC solver."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import uuid
from pathlib import Path
from typing import Any, Mapping

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.distance_milp import get_code_matrices
from scripts.audit_direction_pool import candidate_from_stage2, canonical_digest
from scripts.screen_frontier_candidate import build_candidate_code


def _atomic_matrix(path: Path, matrix: np.ndarray) -> str:
    value = np.asarray(matrix, dtype=np.uint8) & 1
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(
        f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp",
    )
    try:
        with temporary.open("w", encoding="ascii") as stream:
            np.savetxt(stream, value, fmt="%d")
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _atomic_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(
        f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp",
    )
    try:
        with temporary.open("w", encoding="utf-8") as stream:
            json.dump(value, stream, indent=2, sort_keys=True)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def export_pool(ranked_input: Path, output_dir: Path) -> dict[str, Any]:
    records: list[dict[str, Any]] = []
    seen: set[str] = set()
    with ranked_input.open(encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, start=1):
            if not line.strip():
                continue
            value = json.loads(line)
            if not isinstance(value, dict):
                raise ValueError(f"{ranked_input}:{line_number}: row is not an object")
            audit = value.get("campaign_audit")
            if not isinstance(audit, Mapping) or audit.get("status") != "UNRESOLVED":
                continue
            digest = canonical_digest(value)
            if digest in seen:
                continue
            seen.add(digest)
            candidate = candidate_from_stage2(value)
            code = build_candidate_code(candidate)
            hx, hz, lx, lz = (
                np.asarray(matrix, dtype=np.uint8) & 1
                for matrix in get_code_matrices(code)
            )
            k = int(candidate["k"])
            if not (
                lx.shape == lz.shape == (k, hx.shape[1])
                and not np.any((hx @ lz.T) & 1)
                and not np.any((hz @ lx.T) & 1)
                and np.array_equal(
                    (lx @ lz.T) & 1,
                    np.eye(k, dtype=np.uint8),
                )
            ):
                raise ValueError(
                    f"{digest}: logical bases fail CSS kernel/duality replay"
                )
            stem = f"candidate_{len(records):03d}_{digest[:16]}"
            # DistQLDPC names these by the kernel that defines them rather
            # than by qldpc's Pauli label: Gx is a Z-type representative in
            # ker(Hx)/row(Hz), while Gz is X-type in ker(Hz)/row(Hx).
            matrices = {"Hx": hx, "Hz": hz, "Gx": lz, "Gz": lx}
            hashes = {
                name: _atomic_matrix(output_dir / f"{stem}_{name}.txt", matrix)
                for name, matrix in matrices.items()
            }
            records.append({
                "stem": stem,
                "canonical_digest": digest,
                "candidate": candidate,
                "matrix_sha256": hashes,
                "matrix_shapes": {
                    name: list(matrix.shape) for name, matrix in matrices.items()
                },
            })
    manifest = {
        "schema_version": 1,
        "kind": "qcode-distqldpc-export",
        "source": str(ranked_input.resolve()),
        "candidate_count": len(records),
        "candidates": records,
    }
    _atomic_json(output_dir / "manifest.json", manifest)
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("ranked_input", type=Path)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    manifest = export_pool(args.ranked_input, args.output_dir)
    print(json.dumps({
        "candidate_count": manifest["candidate_count"],
        "output_dir": str(args.output_dir.resolve()),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
