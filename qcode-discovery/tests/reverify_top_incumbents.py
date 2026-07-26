#!/usr/bin/env python3
"""Re-verify top incumbent codes from Campaign 4 with extended MILP timeouts.

These codes had high FOM but the solver couldn't prove optimality within the
initial timeout. We re-run with 10x longer timeouts to either confirm or
tighten the distance.

Usage:
    uv run python scripts/reverify_top_incumbents.py [--workers N]
"""

from __future__ import annotations

import argparse
import json
import logging
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from evaluation.evaluator import evaluate_milp_parallel

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
)
logger = logging.getLogger(__name__)

MILP_RESULTS = "results/campaign4_milp_verified.jsonl"
SAVE_PATH = "results/campaign4_reverified.jsonl"

# Extended timeouts: 3000s per logical, 72000s (20h) total per code
TIMEOUT_PER_LOGICAL = 3000
TOTAL_TIMEOUT = 72000
EARLY_STOP = 4


def load_top_incumbents(path: str, min_fom: float = 8.0) -> list[dict]:
    """Load incumbent codes above min_fom threshold."""
    results = []
    seen = set()
    with open(path) as f:
        for line in f:
            r = json.loads(line)
            if r.get("stage") not in ("milp_incumbent", "milp_promising_timeout"):
                continue
            if r.get("fom", 0) < min_fom:
                continue
            # Deduplicate by (ell, m, sorted terms)
            key = (
                r["ell"], r["m"],
                tuple(sorted(tuple(t) for t in r["A_terms"])),
                tuple(sorted(tuple(t) for t in r["B_terms"])),
            )
            if key in seen:
                continue
            seen.add(key)
            results.append(r)
    results.sort(key=lambda x: -x["fom"])
    return results


def main():
    parser = argparse.ArgumentParser(description="Re-verify top incumbents")
    parser.add_argument("--workers", type=int, default=None,
                        help="Number of parallel workers (default: cpu_count - 2)")
    parser.add_argument("--min-fom", type=float, default=8.0,
                        help="Minimum FOM threshold for re-verification")
    args = parser.parse_args()

    logger.info("Loading incumbents from %s (min FOM=%.1f)", MILP_RESULTS, args.min_fom)
    codes = load_top_incumbents(MILP_RESULTS, args.min_fom)
    logger.info("Found %d unique incumbent codes to re-verify", len(codes))

    if not codes:
        logger.error("No incumbents found!")
        return

    for i, c in enumerate(codes):
        logger.info(
            "  %2d. [[%d, %d, %d]] FOM=%.2f  A=%s B=%s",
            i + 1, c["n"], c["k"], c["d"], c["fom"],
            c["A_terms"], c["B_terms"],
        )

    tasks = [
        (c["ell"], c["m"], c["A_terms"], c["B_terms"])
        for c in codes
    ]

    logger.info(
        "Starting re-verification: %d codes, timeout=%ds/logical, %ds total",
        len(tasks), TIMEOUT_PER_LOGICAL, TOTAL_TIMEOUT,
    )

    results = evaluate_milp_parallel(
        tasks,
        milp_timeout_per_logical=TIMEOUT_PER_LOGICAL,
        milp_total_timeout=TOTAL_TIMEOUT,
        milp_early_stop=EARLY_STOP,
        max_workers=args.workers,
        save_path=SAVE_PATH,
    )

    # Summary
    logger.info("=" * 60)
    logger.info("Re-verification Results")
    logger.info("=" * 60)

    results.sort(key=lambda x: -x.get("fom", 0))
    for i, r in enumerate(results):
        exact_flag = "EXACT" if r.get("d_is_exact") else "UB"
        stage = r.get("stage", "?")
        logger.info(
            "  %2d. [[%d, %d, %d]] FOM=%.2f [%s] stage=%s  A=%s B=%s",
            i + 1, r["n"], r["k"], r["d"], r["fom"], exact_flag, stage,
            r["A_terms"], r["B_terms"],
        )

    logger.info("\nResults saved to %s", SAVE_PATH)


if __name__ == "__main__":
    main()
