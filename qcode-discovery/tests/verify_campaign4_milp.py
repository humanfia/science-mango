#!/usr/bin/env python3
"""MILP-verify all codes discovered in Campaign 4, ordered by FOM descending.

Usage:
    uv run python scripts/verify_campaign4_milp.py [--workers N] [--timeout T]

Results are saved incrementally to results/campaign4_milp_verified.jsonl.
Supports resume: re-running skips already-verified codes (MILP cache).
"""

from __future__ import annotations

import argparse
import json
import logging
import os
import sys

# Add project root to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from evaluation.evaluator import evaluate_milp_parallel

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
)
logger = logging.getLogger(__name__)

CAMPAIGN4_JSONL = "results/evolution/ansatz_campaign4/all_codes.jsonl"
SAVE_PATH = "results/campaign4_milp_verified.jsonl"


def load_unique_codes(path: str) -> list[dict]:
    """Load codes from JSONL, deduplicate, return sorted by FOM desc."""
    seen = {}  # key -> best record
    with open(path) as f:
        for line in f:
            r = json.loads(line)
            if r.get("d", 0) == 0 or r.get("k", 0) == 0:
                continue
            # Canonical key: (ell, m, sorted A_terms, sorted B_terms)
            key = (
                r["ell"], r["m"],
                tuple(sorted(tuple(t) for t in r["A_terms"])),
                tuple(sorted(tuple(t) for t in r["B_terms"])),
            )
            if key not in seen or r["fom"] > seen[key]["fom"]:
                seen[key] = r
    codes = list(seen.values())
    codes.sort(key=lambda x: -x["fom"])
    return codes


def main():
    parser = argparse.ArgumentParser(description="MILP-verify Campaign 4 codes")
    parser.add_argument("--workers", type=int, default=None,
                        help="Number of parallel workers (default: cpu_count - 2)")
    parser.add_argument("--timeout-per-logical", type=int, default=300,
                        help="Timeout per logical qubit ILP solve (seconds)")
    parser.add_argument("--total-timeout", type=int, default=7200,
                        help="Total timeout per code (seconds)")
    parser.add_argument("--early-stop", type=int, default=4,
                        help="Stop when d <= this value")
    args = parser.parse_args()

    logger.info("Loading codes from %s", CAMPAIGN4_JSONL)
    codes = load_unique_codes(CAMPAIGN4_JSONL)
    logger.info("Loaded %d unique codes (with d>0), sorted by FOM descending", len(codes))

    if not codes:
        logger.error("No codes found!")
        return

    # Show top 10
    logger.info("Top 10 by BP-OSD FOM:")
    for i, c in enumerate(codes[:10]):
        logger.info(
            "  %2d. [[%d, %d, %d]] FOM=%.1f  A=%s B=%s",
            i + 1, c["n"], c["k"], c["d"], c["fom"],
            c["A_terms"], c["B_terms"],
        )

    # Build task list: (ell, m, A_terms, B_terms), ordered by FOM desc
    tasks = [
        (c["ell"], c["m"], c["A_terms"], c["B_terms"])
        for c in codes
    ]

    logger.info(
        "Starting MILP verification of %d codes with %s workers",
        len(tasks),
        args.workers or f"auto ({min((os.cpu_count() or 4) - 2, 10)})",
    )

    results = evaluate_milp_parallel(
        tasks,
        milp_timeout_per_logical=args.timeout_per_logical,
        milp_total_timeout=args.total_timeout,
        milp_early_stop=args.early_stop,
        max_workers=args.workers,
        save_path=SAVE_PATH,
    )

    # Summary
    exact = [r for r in results if r.get("d_is_exact")]
    incumbent = [r for r in results if r.get("stage") == "milp_incumbent"]
    timeout = [r for r in results if r.get("stage") == "milp_promising_timeout"]
    low_d = [r for r in results if r.get("stage") == "milp_low_d"]

    logger.info("=" * 60)
    logger.info("MILP Verification Summary")
    logger.info("=" * 60)
    logger.info("  Total codes:      %d", len(results))
    logger.info("  Exact distance:   %d", len(exact))
    logger.info("  Incumbent (UB):   %d", len(incumbent))
    logger.info("  Timeout:          %d", len(timeout))
    logger.info("  Low d (<=4):      %d", len(low_d))

    # Top verified codes
    verified = [r for r in results if r.get("d", 0) > 0 and r.get("fom", 0) > 0]
    verified.sort(key=lambda x: -x["fom"])
    if verified:
        logger.info("\nTop 20 MILP-verified codes:")
        for i, r in enumerate(verified[:20]):
            exact_flag = "EXACT" if r.get("d_is_exact") else "UB"
            logger.info(
                "  %2d. [[%d, %d, %d]] FOM=%.1f [%s]  A=%s B=%s",
                i + 1, r["n"], r["k"], r["d"], r["fom"], exact_flag,
                r["A_terms"], r["B_terms"],
            )

    logger.info("\nResults saved to %s", SAVE_PATH)


if __name__ == "__main__":
    main()
