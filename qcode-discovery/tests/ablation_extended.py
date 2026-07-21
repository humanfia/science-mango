#!/usr/bin/env python3
"""Extended ablation baselines: equal-budget random + genetic algorithm.

Addresses reviewer concerns about the original ablation:
1. Equal-budget random: matches Campaign 1's ~213k total candidates (~27k/lattice)
   with multiple seeds to show stability.
2. Genetic algorithm: a simple non-LLM optimizer using tournament selection,
   crossover, and mutation on exponent tuples.

Both use the same Σ_k metric (sum of per-lattice max k) as the original ablation.

Usage::

    uv run python tests/ablation_extended.py
    uv run python tests/ablation_extended.py --random-budget 27000 --ga-budget 27000
    uv run python tests/ablation_extended.py --random-seeds 10
"""

from __future__ import annotations

import argparse
import json
import random as rng
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code, get_code_params_fast, validate_terms

# Same 8 lattices used during evolution's Stage 2
STAGE2_LATTICES = [
    (12, 6), (6, 12),
    (12, 12), (24, 6),
    (15, 12), (30, 6),
    (16, 9), (18, 8),
]


def compute_k(ell: int, m: int, A_terms: list, B_terms: list) -> int:
    """Compute k for a candidate pair. Returns 0 on any error."""
    try:
        validate_terms(ell, m, A_terms, "A")
        validate_terms(ell, m, B_terms, "B")
        code = build_bb_code(ell, m, A_terms, B_terms)
        _, k = get_code_params_fast(code)
        return k
    except Exception:
        return 0


def random_trinomial(ell: int, m: int) -> list[tuple[int, int]]:
    """Generate a random trinomial (3 distinct monomials)."""
    monomials = set()
    while len(monomials) < 3:
        monomials.add((rng.randint(0, ell - 1), rng.randint(0, m - 1)))
    return sorted(monomials)


# ── Equal-budget random baseline ─────────────────────────────────────


def run_equal_budget_random(
    lattices: list[tuple[int, int]],
    budget_per_lattice: int,
    seed: int,
) -> dict:
    """Run random baseline with specified budget per lattice."""
    rng.seed(seed)
    result = {
        "name": f"Random ({budget_per_lattice:,}/lattice, seed={seed})",
        "per_lattice": {},
        "total_candidates": 0,
        "sum_max_k": 0,
    }

    for ell, m in lattices:
        lattice_key = f"({ell},{m})"
        n = 2 * ell * m
        t0 = time.time()

        max_k = 0
        n_valid = 0
        seen = set()

        for _ in range(budget_per_lattice):
            A = random_trinomial(ell, m)
            B = random_trinomial(ell, m)
            key = (tuple(A), tuple(B))
            if key in seen:
                continue
            seen.add(key)

            k = compute_k(ell, m, A, B)
            if k > 0:
                n_valid += 1
                max_k = max(max_k, k)

        elapsed = time.time() - t0
        n_evaluated = len(seen)

        result["per_lattice"][lattice_key] = {
            "n": n,
            "n_candidates": n_evaluated,
            "n_valid": n_valid,
            "max_k": max_k,
            "time_s": round(elapsed, 2),
        }
        result["total_candidates"] += n_evaluated
        result["sum_max_k"] += max_k

        print(f"  {lattice_key} (n={n}): {n_evaluated} candidates, "
              f"{n_valid} valid, max_k={max_k}, {elapsed:.1f}s")

    return result


# ── Genetic algorithm baseline ───────────────────────────────────────


def ga_search(
    ell: int,
    m: int,
    budget: int,
    pop_size: int = 200,
    tournament_size: int = 5,
    crossover_rate: float = 0.7,
    mutation_rate: float = 0.3,
) -> dict:
    """Simple genetic algorithm for finding high-k trinomial pairs.

    Representation: (A_terms, B_terms) each a sorted list of 3 (x,y) tuples.
    Fitness: k value of the resulting BB code.
    Selection: tournament.
    Crossover: swap A or B between parents, or swap individual terms.
    Mutation: randomly change one exponent in one term.
    """
    n_gens = max(1, budget // pop_size)
    total_evals = 0

    # Initialize population randomly
    population = []
    fitnesses = []
    best_k = 0

    for _ in range(pop_size):
        A = random_trinomial(ell, m)
        B = random_trinomial(ell, m)
        k = compute_k(ell, m, A, B)
        population.append((A, B))
        fitnesses.append(k)
        best_k = max(best_k, k)
        total_evals += 1

    def tournament_select():
        """Select individual via tournament."""
        indices = rng.sample(range(len(population)), tournament_size)
        best_idx = max(indices, key=lambda i: fitnesses[i])
        return population[best_idx]

    def crossover(p1, p2):
        """Crossover two parents."""
        A1, B1 = p1
        A2, B2 = p2
        r = rng.random()
        if r < 0.33:
            # Swap A polynomials
            child = (A2[:], B1[:])
        elif r < 0.66:
            # Swap B polynomials
            child = (A1[:], B2[:])
        else:
            # Mix terms: take some A terms from p1, rest from p2
            idx = rng.randint(0, 2)
            new_A = list(A1)
            new_A[idx] = A2[idx]
            # Ensure 3 distinct monomials
            if len(set(new_A)) < 3:
                new_A = A1[:]
            new_A = sorted(set(new_A))[:3]
            if len(new_A) < 3:
                new_A = A1[:]
            child = (new_A, B1[:])
        return child

    def mutate(individual):
        """Mutate one exponent in one term."""
        A, B = [list(x) for x in individual]

        # Pick A or B
        if rng.random() < 0.5:
            target = A
            max_x, max_y = ell, m
        else:
            target = B
            max_x, max_y = ell, m

        # Pick a term to mutate
        idx = rng.randint(0, 2)
        old = target[idx]

        # Mutate x or y exponent
        if rng.random() < 0.5:
            new_x = rng.randint(0, max_x - 1)
            new_term = (new_x, old[1])
        else:
            new_y = rng.randint(0, max_y - 1)
            new_term = (old[0], new_y)

        target[idx] = new_term

        # Ensure 3 distinct
        if len(set(target)) < 3:
            return (sorted(A), sorted(B))  # Skip if collision

        return (sorted(A), sorted(B))

    # Evolution loop
    for gen in range(n_gens):
        if total_evals >= budget:
            break

        new_pop = []
        new_fit = []

        # Elitism: keep top 10%
        n_elite = max(1, pop_size // 10)
        elite_indices = sorted(range(len(population)),
                               key=lambda i: fitnesses[i], reverse=True)[:n_elite]
        for idx in elite_indices:
            new_pop.append(population[idx])
            new_fit.append(fitnesses[idx])

        # Generate rest via crossover + mutation
        while len(new_pop) < pop_size and total_evals < budget:
            p1 = tournament_select()
            p2 = tournament_select()

            if rng.random() < crossover_rate:
                child = crossover(p1, p2)
            else:
                child = (p1[0][:], p1[1][:])

            if rng.random() < mutation_rate:
                child = mutate(child)

            A, B = child
            k = compute_k(ell, m, A, B)
            new_pop.append(child)
            new_fit.append(k)
            best_k = max(best_k, k)
            total_evals += 1

        population = new_pop
        fitnesses = new_fit

    return {
        "max_k": best_k,
        "total_evals": total_evals,
        "n_gens": n_gens,
    }


def run_ga_baseline(
    lattices: list[tuple[int, int]],
    budget_per_lattice: int,
    pop_size: int,
    seed: int,
) -> dict:
    """Run GA baseline on all lattices."""
    rng.seed(seed)
    np.random.seed(seed)

    result = {
        "name": f"GA (pop={pop_size}, {budget_per_lattice:,}/lattice)",
        "per_lattice": {},
        "total_candidates": 0,
        "sum_max_k": 0,
    }

    for ell, m in lattices:
        lattice_key = f"({ell},{m})"
        n = 2 * ell * m
        t0 = time.time()

        ga_result = ga_search(
            ell, m,
            budget=budget_per_lattice,
            pop_size=pop_size,
        )

        elapsed = time.time() - t0
        max_k = ga_result["max_k"]

        result["per_lattice"][lattice_key] = {
            "n": n,
            "n_candidates": ga_result["total_evals"],
            "max_k": max_k,
            "n_gens": ga_result["n_gens"],
            "time_s": round(elapsed, 2),
        }
        result["total_candidates"] += ga_result["total_evals"]
        result["sum_max_k"] += max_k

        print(f"  {lattice_key} (n={n}): {ga_result['total_evals']} evals, "
              f"{ga_result['n_gens']} gens, max_k={max_k}, {elapsed:.1f}s")

    return result


# ── Multi-seed random aggregation ────────────────────────────────────


def run_multiseed_random(
    lattices: list[tuple[int, int]],
    budget_per_lattice: int,
    seeds: list[int],
) -> dict:
    """Run equal-budget random with multiple seeds and aggregate."""
    all_runs = []
    for seed in seeds:
        print(f"\n  --- Random seed={seed} ---")
        run = run_equal_budget_random(lattices, budget_per_lattice, seed)
        all_runs.append(run)

    # Aggregate: per-lattice max_k statistics across seeds
    sigma_k_values = [r["sum_max_k"] for r in all_runs]
    per_lattice_maxk = {}
    for ell, m in lattices:
        key = f"({ell},{m})"
        values = [r["per_lattice"][key]["max_k"] for r in all_runs]
        per_lattice_maxk[key] = {
            "values": values,
            "min": min(values),
            "max": max(values),
            "mean": round(np.mean(values), 1),
            "std": round(np.std(values), 1),
        }

    return {
        "name": f"Random ({budget_per_lattice:,}/lattice, {len(seeds)} seeds)",
        "n_seeds": len(seeds),
        "seeds": seeds,
        "sigma_k_values": sigma_k_values,
        "sigma_k_mean": round(np.mean(sigma_k_values), 1),
        "sigma_k_std": round(np.std(sigma_k_values), 1),
        "sigma_k_min": min(sigma_k_values),
        "sigma_k_max": max(sigma_k_values),
        "per_lattice_stats": per_lattice_maxk,
        "individual_runs": all_runs,
    }


def run_multiseed_ga(
    lattices: list[tuple[int, int]],
    budget_per_lattice: int,
    pop_size: int,
    seeds: list[int],
) -> dict:
    """Run GA with multiple seeds and aggregate."""
    all_runs = []
    for seed in seeds:
        print(f"\n  --- GA seed={seed} ---")
        run = run_ga_baseline(lattices, budget_per_lattice, pop_size, seed)
        all_runs.append(run)

    sigma_k_values = [r["sum_max_k"] for r in all_runs]
    per_lattice_maxk = {}
    for ell, m in lattices:
        key = f"({ell},{m})"
        values = [r["per_lattice"][key]["max_k"] for r in all_runs]
        per_lattice_maxk[key] = {
            "values": values,
            "min": min(values),
            "max": max(values),
            "mean": round(np.mean(values), 1),
            "std": round(np.std(values), 1),
        }

    return {
        "name": f"GA (pop={pop_size}, {budget_per_lattice:,}/lattice, {len(seeds)} seeds)",
        "n_seeds": len(seeds),
        "seeds": seeds,
        "pop_size": pop_size,
        "sigma_k_values": sigma_k_values,
        "sigma_k_mean": round(np.mean(sigma_k_values), 1),
        "sigma_k_std": round(np.std(sigma_k_values), 1),
        "sigma_k_min": min(sigma_k_values),
        "sigma_k_max": max(sigma_k_values),
        "per_lattice_stats": per_lattice_maxk,
        "individual_runs": all_runs,
    }


def main():
    parser = argparse.ArgumentParser(
        description="Extended ablation: equal-budget random + GA baselines"
    )
    parser.add_argument("--random-budget", type=int, default=27000,
                        help="Random candidates per lattice (default: 27000)")
    parser.add_argument("--ga-budget", type=int, default=27000,
                        help="GA evaluations per lattice (default: 27000)")
    parser.add_argument("--ga-pop", type=int, default=200,
                        help="GA population size (default: 200)")
    parser.add_argument("--random-seeds", type=int, default=5,
                        help="Number of random seeds (default: 5)")
    parser.add_argument("--ga-seeds", type=int, default=5,
                        help="Number of GA seeds (default: 5)")
    parser.add_argument("--output", type=str,
                        default="results/ablation_extended.json",
                        help="Output JSON file")
    args = parser.parse_args()

    seeds = list(range(42, 42 + max(args.random_seeds, args.ga_seeds)))

    print("=" * 70)
    print("EXTENDED ABLATION BASELINES")
    print("=" * 70)
    print(f"Lattices: {len(STAGE2_LATTICES)}")
    print(f"Random budget: {args.random_budget:,}/lattice × {args.random_seeds} seeds")
    print(f"GA budget: {args.ga_budget:,}/lattice × {args.ga_seeds} seeds "
          f"(pop={args.ga_pop})")

    t_start = time.time()

    # Equal-budget random
    print(f"\n{'='*70}")
    print(f"EQUAL-BUDGET RANDOM ({args.random_budget:,}/lattice)")
    print(f"{'='*70}")
    random_results = run_multiseed_random(
        STAGE2_LATTICES,
        args.random_budget,
        seeds[:args.random_seeds],
    )

    # GA
    print(f"\n{'='*70}")
    print(f"GENETIC ALGORITHM (pop={args.ga_pop}, {args.ga_budget:,}/lattice)")
    print(f"{'='*70}")
    ga_results = run_multiseed_ga(
        STAGE2_LATTICES,
        args.ga_budget,
        args.ga_pop,
        seeds[:args.ga_seeds],
    )

    total_time = time.time() - t_start

    # Summary
    print(f"\n{'='*70}")
    print(f"SUMMARY ({total_time/60:.1f} minutes)")
    print(f"{'='*70}")

    # Reference values from original ablation
    ref = {
        "Random (1k)": 172,
        "Seed": 276,
        "Campaign 2": 464,
        "Campaign 1 = 3": 704,
    }

    print(f"\n  Original arms (from ablation_k_only.json):")
    for name, sk in ref.items():
        print(f"    {name:25s}  Σ_k = {sk}")

    print(f"\n  Equal-budget Random ({args.random_budget:,}/lattice, "
          f"{args.random_seeds} seeds):")
    print(f"    Σ_k: mean={random_results['sigma_k_mean']}, "
          f"std={random_results['sigma_k_std']}, "
          f"range=[{random_results['sigma_k_min']}, {random_results['sigma_k_max']}]")
    print(f"    Per seed: {random_results['sigma_k_values']}")

    print(f"\n  GA (pop={args.ga_pop}, {args.ga_budget:,}/lattice, "
          f"{args.ga_seeds} seeds):")
    print(f"    Σ_k: mean={ga_results['sigma_k_mean']}, "
          f"std={ga_results['sigma_k_std']}, "
          f"range=[{ga_results['sigma_k_min']}, {ga_results['sigma_k_max']}]")
    print(f"    Per seed: {ga_results['sigma_k_values']}")

    # Per-lattice comparison
    print(f"\n  Per-lattice max_k comparison:")
    print(f"  {'Lattice':<12s}  {'Rnd(1k)':>7s}  {'Seed':>6s}  "
          f"{'Rnd(27k)':>10s}  {'GA':>10s}  {'C1=C3':>6s}")
    print(f"  {'-'*12}  {'-'*7}  {'-'*6}  {'-'*10}  {'-'*10}  {'-'*6}")

    # Load original ablation for reference
    orig_path = Path(__file__).parent.parent / "results" / "ablation_k_only.json"
    if orig_path.exists():
        with open(orig_path) as f:
            orig = json.load(f)
        orig_by_name = {r["name"]: r for r in orig}
    else:
        orig_by_name = {}

    for ell, m in STAGE2_LATTICES:
        key = f"({ell},{m})"
        n = 2 * ell * m
        rnd1k = orig_by_name.get("Random", {}).get("per_lattice", {}).get(key, {}).get("max_k", "?")
        seed_k = orig_by_name.get("Seed", {}).get("per_lattice", {}).get(key, {}).get("max_k", "?")
        c1_k = orig_by_name.get("Campaign 1 (Flash)", {}).get("per_lattice", {}).get(key, {}).get("max_k", "?")

        rnd_stats = random_results["per_lattice_stats"][key]
        ga_stats = ga_results["per_lattice_stats"][key]

        rnd_str = f"{rnd_stats['mean']:.0f}±{rnd_stats['std']:.0f}"
        ga_str = f"{ga_stats['mean']:.0f}±{ga_stats['std']:.0f}"

        print(f"  {key:<7s} n={n:<4d}  {rnd1k:>7}  {seed_k:>6}  "
              f"{rnd_str:>10s}  {ga_str:>10s}  {c1_k:>6}")

    # Save
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    results = {
        "random_equal_budget": random_results,
        "ga": ga_results,
        "metadata": {
            "random_budget_per_lattice": args.random_budget,
            "ga_budget_per_lattice": args.ga_budget,
            "ga_pop_size": args.ga_pop,
            "n_random_seeds": args.random_seeds,
            "n_ga_seeds": args.ga_seeds,
            "lattices": [list(l) for l in STAGE2_LATTICES],
            "total_time_s": round(total_time, 1),
        },
    }
    with open(output_path, "w") as f:
        json.dump(results, f, indent=2, default=list)
    print(f"\nResults saved to {output_path}")


if __name__ == "__main__":
    main()
