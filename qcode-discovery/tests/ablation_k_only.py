#!/usr/bin/env python3
"""K-only ablation study: evaluate generators using deterministic k metrics.

Since ILP verification reveals that BP-OSD distance estimates are unreliable,
this script re-evaluates the ablation using the deterministic k-only metric.
k is computed exactly via GF(2) rank -- no stochasticity, no error bars needed.

Arms:
  - Seed: the hand-crafted seed generator (evolve/seed_solution.py)
  - Campaign 1 best: single-model evolution (Gemini Flash, 100 iters)
  - Campaign 2 best: ensemble evolution (3 models, 251 iters, pop=100)
  - Campaign 3 best: ensemble evolution (3 models, 500 iters, pop=1000)
  - Random: uniform random trinomial pairs (baseline)

Usage::

    uv run python tests/ablation_k_only.py
    uv run python tests/ablation_k_only.py --random-samples 2000  # more random samples
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code, get_code_params_fast, validate_terms

# Same 8 lattices used during evolution's Stage 2
STAGE2_LATTICES = [
    (12, 6), (6, 12),
    (12, 12), (24, 6),
    (15, 12), (30, 6),
    (16, 9), (18, 8),
]

# Generator programs to evaluate
ROOT = Path(__file__).resolve().parent.parent
GENERATORS = {
    "Seed": ROOT / "evolve" / "seed_solution.py",
    "Campaign 1 (Flash)": ROOT / "results" / "evolution_gemini3flash_seed42" / "best" / "best_program.py",
    "Campaign 2 (Ensemble)": ROOT / "results" / "evolution" / "run_20260219_203003" / "checkpoints" / "checkpoint_250" / "best_program.py",
    "Campaign 3 (Ensemble)": ROOT / "results" / "evolution" / "run_20260220_060158" / "best" / "best_program.py",
}


def load_generator(path: Path):
    """Dynamically load a generate_candidates function from a program file."""
    spec = importlib.util.spec_from_file_location("gen_module", str(path))
    mod = importlib.util.module_from_spec(spec)
    # The evolved programs import from KNOWN_CODES which is defined in the same file
    spec.loader.exec_module(mod)
    return mod.generate_candidates


def compute_k_for_candidates(ell: int, m: int, candidates: list) -> list[int]:
    """Compute k for each candidate pair at the given lattice. Returns list of k values."""
    k_values = []
    for A_terms, B_terms in candidates:
        try:
            validate_terms(ell, m, A_terms, "A")
            validate_terms(ell, m, B_terms, "B")
            code = build_bb_code(ell, m, A_terms, B_terms)
            n, k = get_code_params_fast(code)
            if k > 0:
                k_values.append(k)
        except Exception:
            continue
    return k_values


def generate_random_candidates(ell: int, m: int, n_samples: int) -> list:
    """Generate uniform random trinomial pairs."""
    candidates = []
    seen = set()
    for _ in range(n_samples):
        A = sorted(set((random.randint(0, ell - 1), random.randint(0, m - 1)) for _ in range(10)))[:3]
        B = sorted(set((random.randint(0, ell - 1), random.randint(0, m - 1)) for _ in range(10)))[:3]
        if len(A) == 3 and len(B) == 3:
            key = (tuple(A), tuple(B))
            if key not in seen:
                seen.add(key)
                candidates.append((A, B))
    return candidates


def evaluate_arm(name: str, gen_fn, lattices: list[tuple[int, int]]) -> dict:
    """Evaluate a generator on all lattices using k-only metrics."""
    result = {
        "name": name,
        "per_lattice": {},
        "total_candidates": 0,
        "total_valid_k_gt_0": 0,
        "total_high_k": 0,  # k > 12
        "sum_max_k": 0,
        "lattices_with_high_k": 0,
        "max_k_overall": 0,
        "distinct_k_values": set(),
    }

    for ell, m in lattices:
        lattice_key = f"({ell},{m})"
        t0 = time.time()
        try:
            candidates = gen_fn(ell, m)
        except Exception as e:
            print(f"  {lattice_key}: generator error: {e}")
            result["per_lattice"][lattice_key] = {
                "n_candidates": 0, "n_valid": 0, "max_k": 0,
                "high_k_count": 0, "distinct_k": [],
            }
            continue

        n_cands = len(candidates)
        k_values = compute_k_for_candidates(ell, m, candidates)
        gen_time = time.time() - t0

        n = 2 * ell * m
        max_k = max(k_values) if k_values else 0
        high_k = [k for k in k_values if k > 12]
        distinct_k = sorted(set(k_values))

        result["per_lattice"][lattice_key] = {
            "n": n,
            "n_candidates": n_cands,
            "n_valid": len(k_values),
            "max_k": max_k,
            "high_k_count": len(high_k),
            "distinct_k": distinct_k,
            "time_s": round(gen_time, 2),
        }

        result["total_candidates"] += n_cands
        result["total_valid_k_gt_0"] += len(k_values)
        result["total_high_k"] += len(high_k)
        result["sum_max_k"] += max_k
        if max_k > 12:
            result["lattices_with_high_k"] += 1
        result["max_k_overall"] = max(result["max_k_overall"], max_k)
        result["distinct_k_values"].update(k_values)

        print(f"  {lattice_key} (n={n}): {n_cands} candidates, "
              f"{len(k_values)} valid, max_k={max_k}, "
              f"high_k={len(high_k)}, {gen_time:.1f}s")

    result["n_distinct_k_values"] = len(result["distinct_k_values"])
    result["distinct_k_values"] = sorted(result["distinct_k_values"])

    return result


def print_summary_table(results: list[dict]):
    """Print a summary table comparing all arms."""
    print(f"\n{'='*90}")
    print(f"  K-ONLY ABLATION SUMMARY")
    print(f"{'='*90}")
    print(f"  {'Arm':<28s}  {'Cands':>7s}  {'Valid':>6s}  {'High-k':>6s}  "
          f"{'Latt>12':>7s}  {'ΣmaxK':>6s}  {'maxK':>5s}  {'#dist':>5s}")
    print(f"  {'-'*28}  {'-'*7}  {'-'*6}  {'-'*6}  "
          f"{'-'*7}  {'-'*6}  {'-'*5}  {'-'*5}")

    for r in results:
        print(f"  {r['name']:<28s}  {r['total_candidates']:>7d}  "
              f"{r['total_valid_k_gt_0']:>6d}  {r['total_high_k']:>6d}  "
              f"{r['lattices_with_high_k']:>5d}/8  "
              f"{r['sum_max_k']:>6d}  {r['max_k_overall']:>5d}  "
              f"{r['n_distinct_k_values']:>5d}")

    # Per-lattice max k comparison
    print(f"\n  Per-lattice max k:")
    print(f"  {'Lattice':<12s}", end="")
    for r in results:
        short = r["name"][:14]
        print(f"  {short:>14s}", end="")
    print()
    print(f"  {'-'*12}", end="")
    for _ in results:
        print(f"  {'-'*14}", end="")
    print()

    for ell, m in STAGE2_LATTICES:
        key = f"({ell},{m})"
        n = 2 * ell * m
        print(f"  {key:<7s} n={n:<4d}", end="")
        for r in results:
            mk = r["per_lattice"].get(key, {}).get("max_k", 0)
            print(f"  {mk:>14d}", end="")
        print()


def main():
    parser = argparse.ArgumentParser(description="K-only ablation study")
    parser.add_argument("--random-samples", type=int, default=1000,
                        help="Random candidates per lattice (default: 1000)")
    parser.add_argument("--random-seed", type=int, default=42,
                        help="Random seed for reproducibility")
    parser.add_argument("--output", type=str,
                        default="results/ablation_k_only.json",
                        help="Output JSON file")
    args = parser.parse_args()

    random.seed(args.random_seed)

    all_results = []

    # Evaluate each evolved generator
    for name, path in GENERATORS.items():
        if not path.exists():
            print(f"\nSkipping {name}: {path} not found")
            continue
        print(f"\n--- {name} ---")
        print(f"  Source: {path.relative_to(ROOT)}")
        gen_fn = load_generator(path)
        result = evaluate_arm(name, gen_fn, STAGE2_LATTICES)
        all_results.append(result)

    # Random baseline
    print(f"\n--- Random (uniform, {args.random_samples}/lattice) ---")
    def random_gen(ell, m):
        return generate_random_candidates(ell, m, args.random_samples)

    result = evaluate_arm("Random", random_gen, STAGE2_LATTICES)
    all_results.append(result)

    # Print summary
    print_summary_table(all_results)

    # Save JSON
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        json.dump(all_results, f, indent=2, default=list)
    print(f"\nResults saved to {output_path}")


if __name__ == "__main__":
    main()
