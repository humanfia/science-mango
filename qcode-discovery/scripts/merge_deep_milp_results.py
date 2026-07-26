#!/usr/bin/env python3
"""Merge deep MILP evidence into the PBB publication catalog.

This keeps the publication JSONL self-contained: the top-level ``d``/``fom``
fields stay aligned with the best retained distance, while deep-MILP-specific
evidence remains available as ``d_deep_milp`` and per-logical details.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DEEP_FIELDS = [
    "d_deep_milp",
    "d_original",
    "fom_deep",
    "milp_exact_deep",
    "per_logical",
    "logicals_optimal",
    "logicals_incumbent",
    "logicals_failed",
    "total_logicals",
    "deep_milp_time_s",
    "timeout_per_logical",
]


def load_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def merge_rows(publication_rows: list[dict], deep_rows: list[dict]) -> tuple[list[dict], int]:
    deep_by_hash = {row["bliss_hash"]: row for row in deep_rows if row.get("bliss_hash")}
    merged = []
    matched = 0

    for row in publication_rows:
        deep = deep_by_hash.get(row.get("bliss_hash"))
        if not deep:
            normalize_exact_flags(row)
            merged.append(row)
            continue

        matched += 1
        for field in DEEP_FIELDS:
            if field in deep:
                row[field] = deep[field]
        if "verified_at" in deep:
            row["deep_verified_at"] = deep["verified_at"]

        d = int(deep.get("d_deep_milp", row["d"]))
        row["d"] = d
        row["fom"] = round(row["k"] * d * d / row["n"], 4)
        row["d_method"] = "deep_milp"
        row["d_over_sqrtn"] = round(d / (row["n"] ** 0.5), 3)

        exact = bool(deep.get("milp_exact_deep"))
        row["d_is_exact"] = exact
        row["d_is_upper_bound"] = not exact
        row["publication_quality"] = exact
        if exact:
            row["trust_level"] = "EXACT"

        if isinstance(row.get("d_milp"), (int, float)) and d < row["d_milp"]:
            row.setdefault("d_milp_initial", row["d_milp"])
            row["d_milp"] = d

        normalize_exact_flags(row)
        merged.append(row)

    return merged, matched


def normalize_exact_flags(row: dict) -> None:
    """Keep top-level exact/upper-bound booleans aligned with trust level."""
    if row.get("trust_level") == "EXACT":
        row["d_is_exact"] = True
        row["d_is_upper_bound"] = False
        row["publication_quality"] = True
    elif row.get("trust_level") in {"TRUSTED", "PARTIAL", "UNTRUSTED"}:
        row["d_is_exact"] = False
        row["d_is_upper_bound"] = True
        row.setdefault("publication_quality", False)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--publication",
        type=Path,
        default=Path("results/campaign7_publication_merged.jsonl"),
    )
    parser.add_argument(
        "--deep",
        type=Path,
        default=Path("results/campaign7_deep_milp.jsonl"),
    )
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()

    publication_rows = load_jsonl(args.publication)
    deep_rows = load_jsonl(args.deep)
    merged, matched = merge_rows(publication_rows, deep_rows)

    output = args.output or args.publication
    output.write_text("\n".join(json.dumps(row) for row in merged) + "\n")
    print(f"Merged deep MILP evidence for {matched} rows into {output}")


if __name__ == "__main__":
    main()
