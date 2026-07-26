#!/usr/bin/env python3
"""Verify that GA-found high-k codes have d ≤ 2.

Reproduces the GA from ablation_extended.py and checks all codes
with k > Campaign 1's max at each lattice for weight-2 logicals.
"""
import random as rng
import sys
import numpy as np
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from evaluation.bb_code import build_bb_code, get_code_params_fast

STAGE2_LATTICES = [
    (12, 6), (6, 12), (12, 12), (24, 6),
    (15, 12), (30, 6), (16, 9), (18, 8),
]

# Campaign 1 max_k per lattice (from ablation_k_only.json)
C1_MAX_K = {
    (12, 6): 64, (6, 12): 64, (12, 12): 128, (24, 6): 128,
    (15, 12): 160, (30, 6): 160, (16, 9): 0, (18, 8): 0,
}


def random_trinomial(ell, m):
    s = set()
    while len(s) < 3:
        s.add((rng.randint(0, ell - 1), rng.randint(0, m - 1)))
    return sorted(s)


def check_weight2_logicals(code, n, k):
    """Check for weight-2 logical operators. Returns (found, qubit_pair)."""
    hz = np.array(code.matrix_z, dtype=np.uint8)
    logicals = np.array(code.get_logical_ops(), dtype=np.uint8)
    log_z = logicals[k:, n:]

    # Weight-1 check first
    for i in range(n):
        e = np.zeros(n, dtype=np.uint8)
        e[i] = 1
        syn = (hz @ e) % 2
        if np.all(syn == 0) and np.any((log_z @ e) % 2):
            return True, (i,), 1

    # Weight-2 check
    for i in range(n):
        for j in range(i + 1, n):
            e = np.zeros(n, dtype=np.uint8)
            e[i] = 1
            e[j] = 1
            syn = (hz @ e) % 2
            if np.all(syn == 0) and np.any((log_z @ e) % 2):
                return True, (i, j), 2

    return False, None, None


def ga_search_with_tracking(ell, m, budget=10000, pop_size=200, seed=42):
    """Run GA and return all high-k codes found."""
    rng.seed(seed)
    np.random.seed(seed)
    c1_max = C1_MAX_K.get((ell, m), 0)

    # Track best codes (those exceeding C1)
    high_k_codes = []
    best_k = 0

    # Initialize
    population = []
    fitnesses = []
    for _ in range(pop_size):
        A = random_trinomial(ell, m)
        B = random_trinomial(ell, m)
        try:
            code = build_bb_code(ell, m, A, B)
            _, k = get_code_params_fast(code)
        except:
            k = 0
        population.append((A, B))
        fitnesses.append(k)
        if k > best_k:
            best_k = k
        if k > c1_max and k > 0:
            high_k_codes.append((A, B, k))

    n_gens = max(1, budget // pop_size)
    total_evals = pop_size

    for gen in range(n_gens):
        if total_evals >= budget:
            break
        new_pop = []
        new_fit = []

        # Elitism
        n_elite = max(1, pop_size // 10)
        elite_idx = sorted(range(len(population)),
                           key=lambda i: fitnesses[i], reverse=True)[:n_elite]
        for idx in elite_idx:
            new_pop.append(population[idx])
            new_fit.append(fitnesses[idx])

        while len(new_pop) < pop_size and total_evals < budget:
            t = rng.sample(range(len(population)), 5)
            p1 = population[max(t, key=lambda i: fitnesses[i])]
            t = rng.sample(range(len(population)), 5)
            p2 = population[max(t, key=lambda i: fitnesses[i])]

            if rng.random() < 0.7:
                child = (p2[0], p1[1]) if rng.random() < 0.5 else (p1[0], p2[1])
            else:
                child = (list(p1[0]), list(p1[1]))

            A, B = list(child[0]), list(child[1])
            if rng.random() < 0.3:
                tgt = A if rng.random() < 0.5 else B
                idx = rng.randint(0, 2)
                if rng.random() < 0.5:
                    tgt[idx] = (rng.randint(0, ell - 1), tgt[idx][1])
                else:
                    tgt[idx] = (tgt[idx][0], rng.randint(0, m - 1))

            A = sorted(set(A))[:3]
            B = sorted(set(B))[:3]
            if len(A) < 3 or len(B) < 3:
                new_pop.append(population[elite_idx[0]])
                new_fit.append(fitnesses[elite_idx[0]])
                total_evals += 1
                continue

            try:
                code = build_bb_code(ell, m, A, B)
                _, k = get_code_params_fast(code)
            except:
                k = 0

            new_pop.append((A, B))
            new_fit.append(k)
            total_evals += 1

            if k > best_k:
                best_k = k
            if k > c1_max and k > 0:
                # Only track distinct codes
                if (A, B, k) not in high_k_codes:
                    high_k_codes.append((A, B, k))

        population = new_pop
        fitnesses = new_fit

    return best_k, high_k_codes


def main():
    seeds = [42, 43, 44, 45, 46]
    total_checked = 0
    total_d_le_2 = 0
    total_d_gt_2 = 0

    print("=" * 70)
    print("GA HIGH-K CODE DISTANCE VERIFICATION")
    print("Checking all GA codes with k > Campaign 1's max at each lattice")
    print("=" * 70, flush=True)

    for ell, m in STAGE2_LATTICES:
        n = 2 * ell * m
        c1_max = C1_MAX_K.get((ell, m), 0)
        print(f"\n--- ({ell},{m}) n={n}, C1 max_k={c1_max} ---", flush=True)

        seen_codes = set()

        for seed in seeds:
            best_k, high_k_codes = ga_search_with_tracking(ell, m, seed=seed)

            for A, B, k in high_k_codes:
                key = (tuple(map(tuple, A)), tuple(map(tuple, B)))
                if key in seen_codes:
                    continue
                seen_codes.add(key)

                code = build_bb_code(ell, m, A, B)
                found, pair, weight = check_weight2_logicals(code, n, k)
                total_checked += 1

                if found:
                    total_d_le_2 += 1
                    status = f"d<={weight}"
                else:
                    total_d_gt_2 += 1
                    status = "d>=3 (!)"

                print(f"  seed={seed} k={k:>4d} rate={k/n:.3f} "
                      f"A={A} B={B} → {status}", flush=True)

    print(f"\n{'=' * 70}")
    print(f"SUMMARY: checked {total_checked} codes")
    print(f"  d ≤ 2: {total_d_le_2}")
    print(f"  d ≥ 3: {total_d_gt_2}")
    if total_d_gt_2 == 0:
        print("  ALL GA high-k codes have d ≤ 2 ✓")
    else:
        print(f"  WARNING: {total_d_gt_2} codes have d ≥ 3!")
    print(flush=True)


if __name__ == "__main__":
    main()
