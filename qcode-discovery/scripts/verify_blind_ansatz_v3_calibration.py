#!/usr/bin/env python3
"""Post-seal blind calibration for the anchor-free ansatz-v3 campaign."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parents[1]
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from evolve.seed_solution_twisted_torus_ansatz_v3 import (  # noqa: E402
    _canonical_candidate_key,
    _normalise_support,
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical_sha256(value: Any) -> str:
    return hashlib.sha256(json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")).hexdigest()


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"candidate input must be a regular file: {path}")
    rows = []
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise ValueError(f"invalid candidate JSONL row {number}: {exc}") from exc
        if not isinstance(row, dict):
            raise ValueError(f"candidate JSONL row {number} is not an object")
        rows.append(row)
    return rows


def build_report(candidate_path: Path, anchor_manifest_path: Path) -> dict[str, Any]:
    """Load literature supports only after the searched candidate log is sealed."""

    candidate_path = candidate_path.resolve()
    anchor_manifest_path = anchor_manifest_path.resolve()
    candidate_stat_before = os.stat(candidate_path, follow_symlinks=False)
    candidate_sha256 = _sha256(candidate_path)
    rows = _read_jsonl(candidate_path)
    manifest = json.loads(anchor_manifest_path.read_text(encoding="utf-8"))
    if (
        not isinstance(manifest, dict)
        or manifest.get("schema_version") != 1
        or not isinstance(manifest.get("anchors"), list)
    ):
        raise ValueError("published anchor manifest is invalid")

    candidates_by_geometry: dict[tuple[int, int, int], set[Any]] = {}
    for row in rows:
        ell, m = row.get("ell"), row.get("m")
        geometry = row.get("geometry")
        twist = geometry.get("twist", 0) if isinstance(geometry, dict) else 0
        if type(ell) is not int or type(m) is not int or type(twist) is not int:
            continue
        try:
            key = _canonical_candidate_key(
                row["A_terms"],
                row["B_terms"],
                ell,
                m,
                twist=twist,
            )
        except (KeyError, TypeError, ValueError):
            continue
        candidates_by_geometry.setdefault((ell, m, twist), set()).add(key)

    controls = []
    for anchor in manifest["anchors"]:
        ell, m, twist = anchor["ell"], anchor["m"], anchor["twist"]
        support_a = _normalise_support(
            [(0, 0), (1, 0), anchor["third_a"]],
            ell,
            m,
            twist=twist,
        )
        support_b = _normalise_support(
            [(0, 0), (0, 1), anchor["third_b"]],
            ell,
            m,
            twist=twist,
        )
        anchor_key = _canonical_candidate_key(
            support_a,
            support_b,
            ell,
            m,
            twist=twist,
        )
        reconstructed = anchor_key in candidates_by_geometry.get(
            (ell, m, twist), set()
        )
        controls.append({
            "geometry": [ell, m, twist],
            "published_parameters": [anchor["n"], anchor["k"], anchor["d"]],
            "blind_reconstructed": reconstructed,
            "calibration_credit": int(reconstructed),
            "fitness_credit": 0,
            "novelty_credit": 0,
            "search_coverage_credit": 0,
            "discovery_credit": 0,
        })
    candidate_stat_after = os.stat(candidate_path, follow_symlinks=False)
    if (
        candidate_stat_before.st_dev,
        candidate_stat_before.st_ino,
        candidate_stat_before.st_size,
        candidate_stat_before.st_mtime_ns,
    ) != (
        candidate_stat_after.st_dev,
        candidate_stat_after.st_ino,
        candidate_stat_after.st_size,
        candidate_stat_after.st_mtime_ns,
    ) or _sha256(candidate_path) != candidate_sha256:
        raise ValueError("candidate log changed during post-seal calibration")

    payload = {
        "schema_version": 1,
        "kind": "qcode-ansatz-v3-blind-anchor-calibration",
        "semantics": "post-seal calibration-only; never search coverage or discovery",
        "candidate_log": {
            "path": str(candidate_path),
            "sha256": candidate_sha256,
            "bytes": candidate_stat_after.st_size,
            "rows": len(rows),
        },
        "anchor_manifest": {
            "path": str(anchor_manifest_path),
            "sha256": _sha256(anchor_manifest_path),
            "loaded_after_candidate_log_seal": True,
        },
        "controls": controls,
        "blind_reconstructions": sum(row["blind_reconstructed"] for row in controls),
        "fitness_credit": 0,
        "novelty_credit": 0,
        "search_coverage_credit": 0,
        "discovery_credit": 0,
    }
    return {**payload, "report_sha256": _canonical_sha256(payload)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("candidate_log", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--anchor-manifest",
        type=Path,
        default=PROJECT / "evaluation/twisted_torus_published_anchors.v1.json",
    )
    args = parser.parse_args(argv)
    report = build_report(args.candidate_log, args.anchor_manifest)
    if args.output.exists() or args.output.is_symlink():
        parser.error("output already exists; calibration artifacts are immutable")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
