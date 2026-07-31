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
import math

from evaluation.evaluator import evaluate_batch, evaluate_candidate_milp
from evaluation.results import save_code, update_pareto_front
from evaluation.tracking import RunTracker
from evolve.seed_solution import TARGET_LATTICES, generate_candidates

logger = logging.getLogger(__name__)


def _positive_number(value) -> float:
    if isinstance(value, bool):
        return 0.0
    try:
        number = float(value)
    except (TypeError, ValueError, OverflowError):
        return 0.0
    return number if math.isfinite(number) and number > 0 else 0.0


def _validated_exact_params(result: dict) -> tuple[int, int, int] | None:
    """Validate the integer parameters bound to an exact-distance claim."""
    n = result.get("n")
    k = result.get("k")
    d = result.get("d")
    exact_distance = result.get("exact_distance")
    if (
        type(n) is not int
        or type(k) is not int
        or type(d) is not int
        or type(exact_distance) is not int
        or not (1 <= k <= n)
        or not (1 <= d <= n)
        or exact_distance != d
    ):
        return None
    return n, k, d


def _is_exact_distance_result(result: dict) -> bool:
    """Only exact-distance rows may be reported or persisted as discoveries."""
    return (
        result.get("d_is_exact") is True
        and result.get("distance_status") != "upper_bound"
        and _validated_exact_params(result) is not None
    )


def _certified_fom(result: dict) -> float:
    if not _is_exact_distance_result(result):
        return 0.0
    n, k, d = _validated_exact_params(result)
    return k * d * d / n


def _distance_safe_rank(result: dict) -> tuple[float, float]:
    """Rank without treating a decoder/incumbent upper bound as achievement."""
    exact_fom = _certified_fom(result)
    n = _positive_number(result.get("n"))
    k = _positive_number(result.get("k"))
    return exact_fom, (k / n if n else 0.0)


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

    for field in (
        "fom_target",
        "fom_target_numerator",
        "fom_target_denominator",
        "fom_rejection_cutoff",
        "challenge_rejection_cutoff",
        "minimum_passing_distance",
        "milp_early_stop_objective",
        "milp_effective_early_stop",
        "milp_early_stop_triggered",
        "milp_solver_attempted",
        "fom_target_excluded_by_upper_bound",
        "final_gate_excluded_by_upper_bound",
        "threshold_rejection_proven",
        "threshold_proof_lhs",
        "threshold_proof_rhs",
        "threshold_proof_distance",
        "threshold_proof_source",
        "threshold_proof_witness",
        "audit_evaluator_invocation",
        "symplectic_weight_witness",
        "d_symplectic",
    ):
        if field in milp_result:
            merged[field] = milp_result[field]
    merged["threshold_proof_trusted"] = bool(
        milp_result.get("threshold_rejection_proven") is True
        and milp_result.get("distance_trusted") is True
    )
    merged["bp_osd_d"] = bp_d
    merged["milp_attempted"] = True

    if certified:
        merged["distance_status"] = "exact"
        merged["exact_distance"] = milp_d
        exact_params = _validated_exact_params(merged)
        exact_fom = (
            exact_params[1] * exact_params[2] * exact_params[2]
            / exact_params[0]
            if exact_params is not None
            else 0.0
        )
        if exact_fom:
            merged["fom"] = exact_fom
            merged["fom_upper_bound"] = exact_fom
            merged["exact_fom"] = exact_fom
            merged["fitness_distance_credit"] = exact_fom
            if merged.get("search_status") != "terminal_negative":
                merged["score"] = exact_fom
        else:
            merged["exact_fom"] = None
            merged["fitness_distance_credit"] = 0.0
            merged["score"] = 0.0
    else:
        # Preserve the tightest numerical upper bound as diagnostics only.
        upper_fom = _positive_number(merged.get("fom_upper_bound"))
        if not upper_fom:
            upper_fom = _positive_number(merged.get("fom"))
        if not upper_fom:
            n = _positive_number(merged.get("n"))
            k = _positive_number(merged.get("k"))
            d = _positive_number(merged.get("d"))
            if n and k and d:
                upper_fom = k * d * d / n
        merged["distance_status"] = "upper_bound"
        merged["fom_upper_bound"] = upper_fom or None
        merged["fom"] = upper_fom
        merged["exact_distance"] = None
        merged["exact_fom"] = None
        merged["fitness_distance_credit"] = 0.0
        merged["score"] = 0.0
        merged["search_status"] = (
            "terminal_negative"
            if merged.get("threshold_rejection_proven") is True
            else "unresolved"
        )
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
        "--structural-dedup",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Before saving top candidates, reject codes permutation-equivalent "
             "to the known CSS literature registry using BLISS plus explicit "
             "H_X/H_Z permutation replay (default: enabled).",
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
            ranked.sort(key=_distance_safe_rank, reverse=True)
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
            results.sort(key=_distance_safe_rank, reverse=True)
        if args.structural_dedup:
            from evaluation.structural_dedup import annotate_css_result
            ranked_for_novelty = [
                result for result in results
                if _is_exact_distance_result(result)
            ]
            ranked_for_novelty.sort(
                key=_distance_safe_rank,
                reverse=True,
            )
            for result in ranked_for_novelty[:args.top]:
                result.update(annotate_css_result(result))
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
    top = [
        r for r in all_results
        if _is_exact_distance_result(r) and _certified_fom(r) > 0
    ]
    if args.milp_top > 0:
        top = [r for r in top if r.get("milp_attempted")]
    top.sort(key=_distance_safe_rank, reverse=True)
    if args.structural_dedup:
        from evaluation.structural_dedup import deduplicate_css_results
        top, rejected = deduplicate_css_results(top)
        for duplicate in rejected:
            audit = duplicate["structural_novelty"]
            static = duplicate.get("static_eligibility") or {}
            detail = audit.get("matched_reference") or ",".join(
                static.get("failures", [])
            ) or audit.get("relation")
            logger.info(
                "Candidate rejected by %s: [[%d,%d,%d]] (%s)",
                duplicate.get("structural_rejection", "structural_gate"),
                duplicate["n"], duplicate["k"], duplicate["d"],
                detail,
            )
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
