#!/usr/bin/env python3
"""Ablation study: random trinomial baseline vs seed vs LLM evolution.

Three-arm comparison to demonstrate that LLM-guided mutation adds value
beyond random search:

  Arm 1 (Seed): Evaluate the seed `generate_candidates` function on the
      8 Stage 2 lattices using the same evaluation cascade as evolution.
  Arm 2 (Random): Evaluate N random trinomial pairs per lattice.
  Arm 3 (LLM Evolution): Extract Campaign 1 (Gemini Flash) combined_score
      from the evolution log.

All arms use the same combined_score metric: sum of best credible FOM
per lattice, with trust filtering on d/sqrt(n).

Usage:
    uv run python tests/ablation_random_baseline.py [--random-per-lattice 1000] [--runs 5]
"""
from __future__ import annotations

import argparse
import json
import math
import random
import re
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.evaluator import (
    evaluate_batch,
    DISTANCE_TRUST_RATIO,
    DISTANCE_UNTRUST_RATIO,
)

# Same lattices used by the evolution Stage 2
STAGE2_LATTICES = [
    (12, 6), (6, 12),
    (12, 12), (24, 6),
    (15, 12), (30, 6),
    (16, 9), (18, 8),
]


def compute_combined_score(results: list[dict]) -> dict:
    """Compute combined_score using the same trust filter as evolution.

    Returns dict with combined_score and per-lattice breakdown.
    """
    per_lattice_best: dict[tuple[int, int], float] = {}

    for r in results:
        d_raw = r.get("d", 0)
        k = r.get("k", 0)
        n = r.get("n", 0)
        if k <= 0 or n <= 0:
            continue
        key = (r["ell"], r["m"])
        fallback = k / n
        if d_raw <= 0:
            credible_fom = fallback
        else:
            ratio = d_raw / math.sqrt(n)
            raw_fom = k * d_raw * d_raw / n
            if ratio <= DISTANCE_TRUST_RATIO:
                credible_fom = raw_fom
            elif ratio >= DISTANCE_UNTRUST_RATIO:
                credible_fom = fallback
            else:
                alpha = (DISTANCE_UNTRUST_RATIO - ratio) / (
                    DISTANCE_UNTRUST_RATIO - DISTANCE_TRUST_RATIO
                )
                credible_fom = alpha * raw_fom + (1 - alpha) * fallback

        if credible_fom > per_lattice_best.get(key, 0.0):
            per_lattice_best[key] = credible_fom

    combined = sum(per_lattice_best.values())

    # Summary stats
    valid = [r for r in results if r.get("k", 0) > 0]
    foms = [r.get("fom", 0.0) for r in valid if r.get("fom", 0.0) > 0]
    high_k = [r for r in valid if r.get("k", 0) >= 8]

    return {
        "combined_score": combined,
        "per_lattice": {
            f"({k[0]},{k[1]})": v for k, v in sorted(per_lattice_best.items())
        },
        "num_valid": len(valid),
        "num_high_k": len(high_k),
        "best_fom": max(foms) if foms else 0.0,
        "num_above_12": sum(1 for f in foms if f >= 12.0),
        "lattices_with_valid": len(
            set((r["ell"], r["m"]) for r in valid)
        ),
    }


def compute_deterministic_metrics(quick_results_by_lattice: dict) -> dict:
    """Compute metrics that depend only on k (deterministic, no BP-OSD).

    Args:
        quick_results_by_lattice: {(ell, m): [result_dicts]} from k-screening.

    Returns:
        Dict with max_k per lattice, sum_max_k, etc.
    """
    max_k_per_lattice: dict[tuple[int, int], int] = {}
    total_valid = 0
    total_high_k = 0
    total_candidates = 0
    lattices_with_valid = 0

    for (ell, m), results in sorted(quick_results_by_lattice.items()):
        total_candidates += len(results)
        valid = [r for r in results if r.get("k", 0) > 0]
        high_k = [r for r in valid if r.get("k", 0) >= 8]
        total_valid += len(valid)
        total_high_k += len(high_k)
        best_k = max((r.get("k", 0) for r in results), default=0)
        max_k_per_lattice[(ell, m)] = best_k
        if best_k > 0:
            lattices_with_valid += 1

    return {
        "max_k_per_lattice": {
            f"({k[0]},{k[1]})": v for k, v in sorted(max_k_per_lattice.items())
        },
        "sum_max_k": sum(max_k_per_lattice.values()),
        "total_candidates": total_candidates,
        "num_valid": total_valid,
        "num_high_k": total_high_k,
        "lattices_with_valid": lattices_with_valid,
    }


def random_trinomial(ell: int, m: int) -> list[tuple[int, int]]:
    """Sample 3 distinct monomials uniformly from [0,ell) x [0,m)."""
    monomials: set[tuple[int, int]] = set()
    while len(monomials) < 3:
        monomials.add((random.randint(0, ell - 1), random.randint(0, m - 1)))
    return sorted(monomials)


def select_top_candidates(quick_results: list[dict], n_top: int = 10) -> list[dict]:
    """Select top candidates for distance estimation: diverse k values first."""
    promising = [r for r in quick_results if r.get("k", 0) >= 8]
    promising.sort(key=lambda r: r["k"], reverse=True)
    seen_k: set[int] = set()
    top: list[dict] = []
    for r in promising:
        if r["k"] not in seen_k and len(top) < n_top:
            seen_k.add(r["k"])
            top.append(r)
    for r in promising:
        if len(top) >= n_top:
            break
        if r not in top:
            top.append(r)
    return top


def k_screen_seed() -> tuple[dict, dict]:
    """Phase 1 for seed: generate candidates and k-screen (deterministic).

    Returns:
        (quick_results_by_lattice, top_candidates_by_lattice)
    """
    from evolve.seed_solution import generate_candidates

    quick_by_lattice: dict[tuple[int, int], list[dict]] = {}
    top_by_lattice: dict[tuple[int, int], list[dict]] = {}

    for ell, m in STAGE2_LATTICES:
        candidates = generate_candidates(ell, m)
        quick_results = evaluate_batch(ell, m, candidates, quick=True)
        quick_by_lattice[(ell, m)] = quick_results
        top_by_lattice[(ell, m)] = select_top_candidates(quick_results)

        n_valid = sum(1 for r in quick_results if r.get("k", 0) > 0)
        best_k = max((r.get("k", 0) for r in quick_results), default=0)
        n_cand = len(candidates)
        print(f"    ({ell:>2},{m:>2}): {n_cand} candidates, {n_valid} valid, "
              f"best k={best_k}, top {len(top_by_lattice[(ell, m)])} for distance")

    return quick_by_lattice, top_by_lattice


def k_screen_random(n_per_lattice: int) -> tuple[dict, dict]:
    """Phase 1 for random: generate and k-screen (deterministic with fixed seed).

    Returns:
        (quick_results_by_lattice, top_candidates_by_lattice)
    """
    quick_by_lattice: dict[tuple[int, int], list[dict]] = {}
    top_by_lattice: dict[tuple[int, int], list[dict]] = {}

    for ell, m in STAGE2_LATTICES:
        candidates = []
        for _ in range(n_per_lattice):
            A = random_trinomial(ell, m)
            B = random_trinomial(ell, m)
            candidates.append((A, B))

        quick_results = evaluate_batch(ell, m, candidates, quick=True)
        quick_by_lattice[(ell, m)] = quick_results
        top_by_lattice[(ell, m)] = select_top_candidates(quick_results)

        n_valid = sum(1 for r in quick_results if r.get("k", 0) > 0)
        best_k = max((r.get("k", 0) for r in quick_results), default=0)
        print(f"    ({ell:>2},{m:>2}): {n_per_lattice} candidates, {n_valid} valid, "
              f"best k={best_k}, top {len(top_by_lattice[(ell, m)])} for distance")

    return quick_by_lattice, top_by_lattice


def run_distance_estimation(
    top_by_lattice: dict[tuple[int, int], list[dict]],
    quick_by_lattice: dict[tuple[int, int], list[dict]],
) -> list[dict]:
    """Phase 2: Run distance estimation on top candidates (stochastic).

    Returns all results (distance-estimated top + k-only remainder).
    """
    all_results = []

    for (ell, m), top in sorted(top_by_lattice.items()):
        if top:
            top_candidates = [(r["A_terms"], r["B_terms"]) for r in top]
            dist_results = evaluate_batch(
                ell, m, top_candidates,
                quick=False,
                quick_trials=1000,
                fom_threshold_refine=6.0,
                fom_threshold_exact=float("inf"),
            )
            all_results.extend(dist_results)

        # Include k-only results for counting
        quick_only = [
            r for r in quick_by_lattice[(ell, m)]
            if r.get("k", 0) > 0 and r not in top
        ]
        all_results.extend(quick_only)

    return all_results


def run_arm3_evolution() -> dict:
    """Arm 3: Extract LLM evolution data from Campaign 1 log."""
    root = Path(__file__).resolve().parent.parent
    log_path = root / "results/evolution_gemini3flash_seed42/logs/openevolve_20260217_163127.log"

    if not log_path.exists():
        print(f"  WARNING: Log file not found: {log_path}")
        return {"error": "log not found"}

    pattern = re.compile(r"Metrics: combined_score=([\d.]+)")
    scores = []
    with open(log_path) as f:
        for line in f:
            match = pattern.search(line)
            if match:
                scores.append(float(match.group(1)))

    if not scores:
        return {"error": "no scores in log"}

    running_best = []
    best = 0.0
    for s in scores:
        if s > best:
            best = s
        running_best.append(best)

    seed_score = scores[0] if scores else 0.0
    final_best = running_best[-1] if running_best else 0.0

    milestones = {}
    for target in [200, 250, 300, 320, 327]:
        for i, rb in enumerate(running_best):
            if rb >= target:
                milestones[target] = i
                break

    return {
        "combined_score": final_best,
        "seed_score": seed_score,
        "num_iterations": len(scores),
        "milestones": milestones,
    }


def main():
    parser = argparse.ArgumentParser(description="Ablation study")
    parser.add_argument("--random-per-lattice", type=int, default=1000,
                        help="Random candidates per lattice (default 1000)")
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--runs", type=int, default=1,
                        help="Number of distance estimation runs (default 1)")
    args = parser.parse_args()

    random.seed(args.seed)

    print("=" * 60)
    print("  ABLATION STUDY: SEED vs RANDOM vs LLM EVOLUTION")
    print(f"  Runs: {args.runs}, Random/lattice: {args.random_per_lattice}")
    print("=" * 60)

    # ---------------------------------------------------------------
    # Phase 1: k-screening (deterministic, runs once)
    # ---------------------------------------------------------------
    print("\n--- Phase 1: k-screening (deterministic) ---")

    print("\n  Arm 1 (Seed):")
    seed_quick, seed_top = k_screen_seed()
    seed_det = compute_deterministic_metrics(seed_quick)

    print("\n  Arm 2 (Random):")
    rand_quick, rand_top = k_screen_random(args.random_per_lattice)
    rand_det = compute_deterministic_metrics(rand_quick)

    print("\n  Arm 3 (LLM Evolution):")
    arm3 = run_arm3_evolution()
    if "combined_score" in arm3 and arm3.get("seed_score", 0) > 0:
        print(f"    Campaign 1: seed {arm3['seed_score']:.1f} → best {arm3['combined_score']:.1f} "
              f"(+{(arm3['combined_score']/arm3['seed_score'] - 1)*100:.0f}%)")

    # ---------------------------------------------------------------
    # Deterministic metrics report
    # ---------------------------------------------------------------
    print("\n" + "=" * 60)
    print("  DETERMINISTIC METRICS (k-only, no BP-OSD dependency)")
    print("=" * 60)
    print(f"  {'Metric':<30} {'Seed':>8} {'Random':>8}")
    print(f"  {'-'*46}")
    print(f"  {'Candidates evaluated':<30} {seed_det['total_candidates']:>8} {rand_det['total_candidates']:>8}")
    print(f"  {'Valid codes (k>0)':<30} {seed_det['num_valid']:>8} {rand_det['num_valid']:>8}")
    print(f"  {'High-k codes (k>=8)':<30} {seed_det['num_high_k']:>8} {rand_det['num_high_k']:>8}")
    print(f"  {'Lattices with valid':<30} {seed_det['lattices_with_valid']:>8} {rand_det['lattices_with_valid']:>8}")
    print(f"  {'Sum of max-k per lattice':<30} {seed_det['sum_max_k']:>8} {rand_det['sum_max_k']:>8}")
    print(f"\n  Max-k per lattice:")
    for key in sorted(seed_det["max_k_per_lattice"].keys()):
        sk = seed_det["max_k_per_lattice"].get(key, 0)
        rk = rand_det["max_k_per_lattice"].get(key, 0)
        print(f"    {key:<10} seed={sk:>3}  random={rk:>3}")

    # ---------------------------------------------------------------
    # Phase 2: distance estimation (stochastic, runs N times)
    # ---------------------------------------------------------------
    n_runs = args.runs
    seed_scores = []
    rand_scores = []
    t0 = time.time()

    for run_idx in range(n_runs):
        print(f"\n--- Phase 2: Distance estimation, run {run_idx + 1}/{n_runs} ---")

        print(f"  Arm 1 (Seed)...", end="", flush=True)
        seed_results = run_distance_estimation(seed_top, seed_quick)
        seed_info = compute_combined_score(seed_results)
        seed_scores.append(seed_info["combined_score"])
        print(f" score={seed_info['combined_score']:.1f}")

        print(f"  Arm 2 (Random)...", end="", flush=True)
        rand_results = run_distance_estimation(rand_top, rand_quick)
        rand_info = compute_combined_score(rand_results)
        rand_scores.append(rand_info["combined_score"])
        print(f" score={rand_info['combined_score']:.1f}")

    elapsed = time.time() - t0

    # ---------------------------------------------------------------
    # Summary
    # ---------------------------------------------------------------
    seed_arr = np.array(seed_scores)
    rand_arr = np.array(rand_scores)

    print("\n" + "=" * 60)
    print("  COMBINED SCORE SUMMARY (stochastic, BP-OSD dependent)")
    print("=" * 60)
    if n_runs == 1:
        print(f"  Seed:      {seed_arr[0]:.1f}")
        print(f"  Random:    {rand_arr[0]:.1f}")
    else:
        print(f"  Seed:      {seed_arr.mean():.1f} ± {seed_arr.std():.1f} "
              f"(range: {seed_arr.min():.1f}-{seed_arr.max():.1f}, n={n_runs})")
        print(f"  Random:    {rand_arr.mean():.1f} ± {rand_arr.std():.1f} "
              f"(range: {rand_arr.min():.1f}-{rand_arr.max():.1f}, n={n_runs})")
    if "combined_score" in arm3:
        print(f"  LLM evo:   {arm3['combined_score']:.1f} (Campaign 1, from log)")

    if n_runs > 1:
        # Paired comparison: seed - random for each run
        diff = seed_arr - rand_arr
        print(f"\n  Seed − Random (paired): {diff.mean():.1f} ± {diff.std():.1f} "
              f"(range: {diff.min():.1f}-{diff.max():.1f})")
        print(f"  Seed > Random in {np.sum(diff > 0)}/{n_runs} runs")

        if "combined_score" in arm3:
            evo_score = arm3["combined_score"]
            print(f"\n  LLM evo − Seed:   {evo_score - seed_arr.mean():.1f} "
                  f"(vs mean seed, always > 0: {np.all(evo_score > seed_arr)})")
            print(f"  LLM evo − Random: {evo_score - rand_arr.mean():.1f} "
                  f"(vs mean random, always > 0: {np.all(evo_score > rand_arr)})")
            max_baseline = max(seed_arr.max(), rand_arr.max())
            print(f"  LLM evo vs best baseline run: {evo_score:.1f} vs {max_baseline:.1f} "
                  f"({evo_score/max_baseline:.2f}x)")

    print(f"\n  Elapsed: {elapsed:.0f}s")

    # ---------------------------------------------------------------
    # Save results
    # ---------------------------------------------------------------
    output = {
        "deterministic": {
            "arm1_seed": seed_det,
            "arm2_random": rand_det,
        },
        "stochastic": {
            "arm1_seed_scores": seed_scores,
            "arm2_random_scores": rand_scores,
            "arm1_seed_mean": float(seed_arr.mean()),
            "arm1_seed_std": float(seed_arr.std()),
            "arm2_random_mean": float(rand_arr.mean()),
            "arm2_random_std": float(rand_arr.std()),
        },
        "arm3_evolution": {k: v for k, v in arm3.items()},
        "config": {
            "random_per_lattice": args.random_per_lattice,
            "seed": args.seed,
            "runs": n_runs,
            "lattices": [list(lat) for lat in STAGE2_LATTICES],
        },
    }
    output_path = Path("results/ablation_study.json")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\n  Saved results to {output_path}")


if __name__ == "__main__":
    main()
