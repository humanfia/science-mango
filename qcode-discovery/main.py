"""CLI entry point for running the BB code evaluation pipeline.

Generates candidate polynomial pairs using the seed
``generate_candidates`` function (or whatever is currently in
``evolve/seed_solution.py``), evaluates them through the multi-stage
cascade (see :mod:`evaluation.evaluator`), and saves the best results
to ``results/discovered_codes.json`` and ``results/pareto_front.json``.

Each ``(ell, m)`` lattice is evaluated as a separate "generation" for
tracking purposes, with per-lattice summaries logged to
``results/runs/<run_id>/generations.jsonl``.

Usage::

    # Quick k-only scan across all 18 target lattices (~30 s)
    uv run python main.py --quick

    # Evaluate specific lattices with distance estimation
    uv run python main.py --lattices 12,6 6,6

    # Full cascade with custom thresholds
    uv run python main.py --lattices 12,6 --quick-trials 200 --fom-threshold-refine 5.0

    # Verbose output
    uv run python main.py --lattices 6,6 --quick -v

CLI options::

    --lattices ELL,M ...      Lattice dimensions (default: all 18 target lattices)
    --quick                   Compute k only, skip distance estimation
    --quick-trials N          BP-OSD trials for initial distance estimate (default: 100)
    --refine-trials N         BP-OSD trials for refined estimate (default: 1000)
    --fom-threshold-refine F  FOM threshold for refined estimation (default: 6.0)
    --fom-threshold-exact F   FOM threshold for exact distance (default: 8.0)
    --top N                   Number of top results to display (default: 10)
    --run-id ID               Run identifier for tracking (auto-generated if not set)
    -v, --verbose             Enable debug logging
"""

from __future__ import annotations

import argparse
import logging

from evaluation.evaluator import evaluate_batch, evaluate_candidate_milp
from evaluation.results import save_code, update_pareto_front
from evaluation.tracking import RunTracker
from evolve.seed_solution import TARGET_LATTICES, generate_candidates

logger = logging.getLogger(__name__)


def _milp_fully_certified(result: dict) -> bool:
    """Return whether MILP or a structural d=2 rule fully certified distance."""
    if result.get("d_is_exact") and (
        result.get("stage") == "self_dual_d2"
        or (result.get("stage") == "symplectic_low_d" and int(result.get("d", 0)) == 2)
    ):
        return True
    details = result.get("milp_details") or {}
    total = int(details.get("total_logicals", 0))
    checked = int(details.get("num_logicals_checked", 0))
    optimal = int(details.get("logicals_optimal", 0))
    return bool(details.get("exact")) and total > 0 and checked == total and optimal == total


def merge_bp_milp_result(bp: dict, milp_result: dict) -> dict:
    """Combine two valid upper bounds without promoting partial MILP to exact."""
    bp_d = int(bp.get("d", 0) or 0)
    milp_d = int(milp_result.get("d", 0) or 0)
    certified = _milp_fully_certified(milp_result)

    if certified:
        merged = dict(milp_result)
        merged["d_is_exact"] = True
        merged["distance_source"] = "milp_exact"
    elif milp_d > 0 and (bp_d <= 0 or milp_d <= bp_d):
        merged = dict(milp_result)
        merged["d_is_exact"] = False
        merged["distance_source"] = "milp_incumbent"
    else:
        merged = dict(bp)
        merged["d_is_exact"] = False
        merged["milp_details"] = milp_result.get("milp_details", {})
        merged["milp_stage"] = milp_result.get("stage")
        merged["distance_source"] = "bp_osd"
        merged["stage"] = "bp_osd_after_milp"

    merged["bp_osd_d"] = bp_d
    merged["milp_attempted"] = True
    return merged


def main():
    parser = argparse.ArgumentParser(
        description="Evaluate bivariate bicycle codes across target lattices."
    )
    parser.add_argument(
        "--lattices", nargs="*", type=str, default=None,
        help="Lattice dimensions as 'ell,m' pairs (e.g. 12,6 9,8). "
             "Defaults to all target lattices.",
    )
    parser.add_argument(
        "--quick", action="store_true",
        help="Quick mode: compute k only, skip distance estimation.",
    )
    parser.add_argument(
        "--quick-trials", type=int, default=100,
        help="Number of BP-OSD trials for initial distance estimate.",
    )
    parser.add_argument(
        "--refine-trials", type=int, default=1000,
        help="Number of BP-OSD trials for refined distance estimate.",
    )
    parser.add_argument(
        "--fom-threshold-refine", type=float, default=6.0,
        help="FOM threshold to trigger refined distance estimation.",
    )
    parser.add_argument(
        "--fom-threshold-exact", type=float, default=8.0,
        help="FOM threshold to trigger exact distance computation.",
    )
    parser.add_argument(
        "--milp-top", type=int, default=0,
        help="Run HiGHS MILP only for the top N BP-OSD candidates per lattice. "
             "When positive, replaces the legacy brute-force exact stage.",
    )
    parser.add_argument(
        "--milp-timeout-per-logical", type=int, default=300,
        help="MILP timeout in seconds for each logical direction.",
    )
    parser.add_argument(
        "--milp-total-timeout", type=int, default=7200,
        help="Total MILP timeout in seconds for each selected code.",
    )
    parser.add_argument(
        "--milp-early-stop", type=int, default=0,
        help="Stop MILP after finding d at or below this value; 0 checks every "
             "logical direction and permits exact certification.",
    )
    parser.add_argument(
        "--top", type=int, default=10,
        help="Number of top results to display.",
    )
    parser.add_argument(
        "--run-id", type=str, default=None,
        help="Run identifier for tracking. Auto-generated if not set.",
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true",
        help="Enable verbose logging.",
    )
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s %(levelname)s %(name)s: %(message)s",
    )

    if args.lattices:
        lattices = []
        for spec in args.lattices:
            ell, m = spec.split(",")
            lattices.append((int(ell), int(m)))
    else:
        lattices = TARGET_LATTICES

    eval_kwargs = dict(
        quick=args.quick,
        quick_trials=args.quick_trials,
        refine_trials=args.refine_trials,
        fom_threshold_refine=args.fom_threshold_refine,
        fom_threshold_exact=args.fom_threshold_exact,
        # Top-N MILP owns expensive certification while OSD-CS remains active.
        skip_exact=args.milp_top > 0,
    )

    # Initialize run tracker
    tracker = RunTracker()
    run_id = tracker.start_run(
        run_id=args.run_id,
        config={"lattices": lattices, **eval_kwargs},
    )
    print(f"Run {run_id}: evaluating {len(lattices)} lattice(s)...")

    # Evaluate each lattice as a "generation" for tracking
    all_results = []
    for gen_idx, (ell, m) in enumerate(lattices):
        candidates = generate_candidates(ell, m)
        logger.info(
            "Lattice (%d, %d): %d candidates, n=%d",
            ell, m, len(candidates), 2 * ell * m,
        )

        tracker.start_generation(gen_idx)
        results = evaluate_batch(ell, m, candidates, **eval_kwargs)
        if not args.quick and args.milp_top > 0:
            ranked = [r for r in results if r.get("k", 0) > 0 and r.get("d", 0) > 0]
            ranked.sort(key=lambda r: r.get("score", float("-inf")), reverse=True)
            replacements = {}
            for bp_result in ranked[:args.milp_top]:
                milp_result = evaluate_candidate_milp(
                    ell, m, bp_result["A_terms"], bp_result["B_terms"],
                    milp_timeout_per_logical=args.milp_timeout_per_logical,
                    milp_total_timeout=args.milp_total_timeout,
                    milp_early_stop=(args.milp_early_stop or None),
                )
                key = (tuple(map(tuple, bp_result["A_terms"])),
                       tuple(map(tuple, bp_result["B_terms"])))
                replacements[key] = merge_bp_milp_result(bp_result, milp_result)
            results = [replacements.get(
                (tuple(map(tuple, r["A_terms"])), tuple(map(tuple, r["B_terms"]))), r
            ) for r in results]
            results.sort(key=lambda r: r.get("score", float("-inf")), reverse=True)
        for r in results:
            tracker.log_evaluation(r)
        summary = tracker.end_generation(gen_idx, results)

        all_results.extend(results)
        print(
            f"  ({ell},{m}) n={2*ell*m}: "
            f"{summary['valid_candidates']}/{summary['total_candidates']} valid, "
            f"best FOM={summary['best_fom']:.2f}"
        )

    run_meta = tracker.end_run()

    # Save and display top results
    top = [r for r in all_results if r.get("score", 0) > 0]
    if args.milp_top > 0:
        top = [r for r in top if r.get("milp_attempted")]
    top.sort(key=lambda r: r["score"], reverse=True)
    top = top[:args.top]
    for r in top:
        save_code(r)
    if top:
        update_pareto_front(top)

    print(f"\nTop {min(len(top), args.top)} codes found:")
    print(f"{'Code':>20s}  {'FOM':>6s}  {'Stage':>16s}")
    print("-" * 48)
    for r in top:
        label = f"[[{r['n']},{r['k']},{r['d']}]]"
        print(f"{label:>20s}  {r['fom']:6.2f}  {r['stage']:>16s}")

    if not top:
        print("  (no codes with positive score found)")

    print(f"\nRun log: {tracker.run_dir}/")
    print(f"  Total evaluations: {run_meta['total_evaluations']}")
    print(f"  Best FOM: {run_meta['best_fom']:.2f}")


if __name__ == "__main__":
    main()
