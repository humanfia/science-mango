"""Code capacity simulations for Table V codes missing from threshold tables.

Three codes from Table V "This work" that lack simulation data:
- [[288,50,8]] CSS (cross-factored, wt-8, lattice 18,8)
- [[144,8,12]] CSS (mixed-monomial, wt-6, lattice 12,6)
- [[360,12,<=20]] PBB non-CSS (lattice 30,6)

Protocol: independent X errors at rate p, BP-OSD (OSD-CS order 7, product-sum,
20 BP iterations), 100,000 shots per rate. Identical to existing simulations.

Decoder hyperparameter rationale:
- product-sum BP is the default in the ``ldpc`` package and was used in
  Bravyi et al. 2024 (arXiv:2308.07915) for threshold simulations of
  related BB codes; we keep a single fixed configuration here so the
  reported threshold is well-defined (an ensemble across product-sum
  and minimum-sum BP would conflate the two).  Our soak-test
  verification (``tests/soak_test.py``) does run both BP variants for
  distance estimation, where the goal is finding low-weight logicals
  rather than estimating a threshold.
- ``max_iter = 20`` is a deliberately modest value: BP iterations
  beyond ~10-20 yield diminishing returns at code-capacity rates while
  multiplying simulation cost; it is comparable to or higher than the
  ``max_iter = 16`` reported in Roffe et al.'s ``ldpc`` documentation
  for similar code sizes.  Increasing it further changes the reported
  LER by less than the Wilson 95% CI at 100,000 shots.

Usage:
    uv run python tests/threshold_simulation_missing.py
    uv run python tests/threshold_simulation_missing.py --shots 10000  # quick test
"""

import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.sparse import csr_matrix

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code
from evaluation.pbb_code import build_pbb_code, get_symplectic_logicals
from ldpc import BpOsdDecoder


# === CSS codes (use build_bb_code) ===
CODES_CSS = [
    {
        "label": "[[288,50,8]] MILP d=8, FOM=11.1 (cross-factored)",
        "ell": 18, "m": 8,
        # A = 1 + y^5 + x + xy^5  (4-term)
        "A_terms": [(0, 0), (0, 5), (1, 0), (1, 5)],
        # B = 1 + y + x^5 + x^5*y  (4-term)
        "B_terms": [(0, 0), (0, 1), (5, 0), (5, 1)],
    },
    {
        "label": "[[144,8,12]] MILP d=12, FOM=8.0 (mixed-monomial)",
        "ell": 12, "m": 6,
        # A = 1 + xy^2 + xy^3
        "A_terms": [(0, 0), (1, 2), (1, 3)],
        # B = 1 + x^2*y^3 + x^3*y^2
        "B_terms": [(0, 0), (2, 3), (3, 2)],
    },
]

# === Non-CSS PBB code (use build_pbb_code) ===
CODES_PBB = [
    {
        # Catalog: code_id 30_6_0260, bliss_hash 5012d8bafff7fd2b
        # C/D values follow paper.tex Table V (post-`migrate_cd_convention.py`).
        "label": "[[360,12,<=20]] PBB (best PBB FOM)",
        "ell": 30, "m": 6,
        # A = x^13*y^4 + x^22*y^2 + x^22*y^3
        "A_terms": [(13, 4), (22, 2), (22, 3)],
        # B = 1 + x^5*y^2 + x^13*y
        "B_terms": [(0, 0), (5, 2), (13, 1)],
        # C = x^13*y^3 + x^22*y^3
        "C_terms": [(13, 3), (22, 3)],
        # D = x^13*y + x^22*y
        "D_terms": [(13, 1), (22, 1)],
    },
]

ERROR_RATES = [0.002, 0.005, 0.008, 0.01, 0.015, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08]
NUM_SHOTS = 100_000


def run_css_simulation(code_spec, error_rates, num_shots, verbose=True):
    """Run code capacity simulation for a CSS BB code."""
    label = code_spec["label"]
    code = build_bb_code(
        code_spec["ell"], code_spec["m"],
        code_spec["A_terms"], code_spec["B_terms"],
    )
    n = code.num_qudits
    k = code.dimension

    if verbose:
        print(f"\n{'=' * 60}")
        print(f"  {label}  n={n}, k={k}")
        print(f"  {len(error_rates)} error rates × {num_shots} shots")
        print(f"{'=' * 60}")

    hz = np.array(code.matrix_z, dtype=np.uint8)
    hz_sparse = csr_matrix(hz)

    logicals = np.array(code.get_logical_ops(), dtype=np.uint8)
    log_z_zpart = logicals[k:, n:]  # k × n binary matrix

    decoder = BpOsdDecoder(
        hz_sparse,
        error_rate=0.01,
        bp_method="product_sum",
        max_iter=20,
        osd_method="osd_cs",
        osd_order=7,
    )

    results = []
    t0 = time.time()

    for p in error_rates:
        t_p = time.time()
        decoder.update_channel_probs(np.full(n, p))

        logical_errors = 0
        for _ in range(num_shots):
            error = (np.random.random(n) < p).astype(np.uint8)
            syndrome = (hz @ error) % 2
            correction = decoder.decode(syndrome)
            residual = (error + correction) % 2
            log_check = (log_z_zpart @ residual) % 2
            if np.any(log_check):
                logical_errors += 1

        ler = logical_errors / num_shots
        elapsed = time.time() - t_p
        uncoded = 1 - (1 - p) ** k

        results.append({
            "p": p,
            "logical_error_rate": ler,
            "logical_errors": logical_errors,
            "num_shots": num_shots,
            "time_s": round(elapsed, 1),
        })

        if verbose:
            marker = " ***" if ler > p else ""
            print(f"  p={p:.4f}  LER={ler:.5f}  uncoded={uncoded:.5f}  ({logical_errors:5d}/{num_shots})  [{elapsed:.1f}s]{marker}")

    total_time = time.time() - t0
    if verbose:
        print(f"  Total: {total_time:.0f}s ({total_time/60:.1f} min)")

    return {
        "label": label,
        "n": n,
        "k": k,
        "ell": code_spec["ell"],
        "m": code_spec["m"],
        "is_css": True,
        "error_rates": results,
        "total_time_s": round(total_time, 1),
    }


def run_pbb_simulation(code_spec, error_rates, num_shots, verbose=True):
    """Run code capacity simulation for a non-CSS PBB code."""
    label = code_spec["label"]
    code = build_pbb_code(
        code_spec["ell"], code_spec["m"],
        code_spec["A_terms"], code_spec["B_terms"],
        code_spec.get("C_terms"), code_spec.get("D_terms"),
    )
    n = code.num_qudits
    k = code.dimension

    if verbose:
        print(f"\n{'=' * 60}")
        print(f"  {label}  n={n}, k={k}")
        print(f"  non-CSS  |  {len(error_rates)} error rates × {num_shots} shots")
        print(f"{'=' * 60}")

    # Non-CSS: extract Z-part of full stabilizer matrix
    stab = np.array(code.matrix, dtype=np.uint8) % 2
    hz = stab[:, n:]  # Z-part of all stabilizers

    # Get symplectic logicals and extract Z-parts
    sym_logicals = get_symplectic_logicals(code)
    log_z_parts = sym_logicals[:, n:].astype(np.uint8)

    if verbose:
        print(f"  Check matrix: {hz.shape[0]} × {hz.shape[1]}")
        print(f"  Logical operators: {log_z_parts.shape[0]} (checking Z-parts)")

    hz_sparse = csr_matrix(hz)

    decoder = BpOsdDecoder(
        hz_sparse,
        error_rate=0.01,
        bp_method="product_sum",
        max_iter=20,
        osd_method="osd_cs",
        osd_order=7,
    )

    results = []
    t0 = time.time()

    for p in error_rates:
        t_p = time.time()
        decoder.update_channel_probs(np.full(n, p))

        logical_errors = 0
        for _ in range(num_shots):
            error = (np.random.random(n) < p).astype(np.uint8)
            syndrome = (hz @ error) % 2
            correction = decoder.decode(syndrome)
            residual = (error + correction) % 2
            log_check = (log_z_parts @ residual) % 2
            if np.any(log_check):
                logical_errors += 1

        ler = logical_errors / num_shots
        elapsed = time.time() - t_p
        uncoded = 1 - (1 - p) ** k

        results.append({
            "p": p,
            "logical_error_rate": ler,
            "logical_errors": logical_errors,
            "num_shots": num_shots,
            "time_s": round(elapsed, 1),
        })

        if verbose:
            marker = " ***" if ler > p else ""
            print(f"  p={p:.4f}  LER={ler:.5f}  uncoded={uncoded:.5f}  ({logical_errors:5d}/{num_shots})  [{elapsed:.1f}s]{marker}")

    total_time = time.time() - t0
    if verbose:
        print(f"  Total: {total_time:.0f}s ({total_time/60:.1f} min)")

    return {
        "label": label,
        "n": n,
        "k": k,
        "ell": code_spec["ell"],
        "m": code_spec["m"],
        "is_css": False,
        "error_rates": results,
        "total_time_s": round(total_time, 1),
    }


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Code capacity simulation for Table V missing codes")
    parser.add_argument("--shots", type=int, default=NUM_SHOTS, help="Shots per error rate")
    parser.add_argument("--css-only", action="store_true", help="Only simulate CSS codes")
    parser.add_argument("--pbb-only", action="store_true", help="Only simulate PBB codes")
    args = parser.parse_args()

    print("Code Capacity Simulation -- Table V Missing Codes")
    print(f"Error rates: {ERROR_RATES}")
    print(f"Shots per rate: {args.shots:,}")

    np.random.seed(42)
    all_results = []
    t_start = time.time()

    if not args.pbb_only:
        for code_spec in CODES_CSS:
            result = run_css_simulation(code_spec, ERROR_RATES, args.shots, verbose=True)
            all_results.append(result)

    if not args.css_only:
        for code_spec in CODES_PBB:
            result = run_pbb_simulation(code_spec, ERROR_RATES, args.shots, verbose=True)
            all_results.append(result)

    total = time.time() - t_start

    # Summary
    print(f"\n{'=' * 70}")
    print(f"SUMMARY ({total/60:.1f} minutes total)")
    print(f"{'=' * 70}")

    for r in all_results:
        print(f"\n{r['label']}  n={r['n']}, k={r['k']}")
        print(f"  {'p':>6s}  {'LER':>8s}  {'p_L':>8s}  {'Uncoded':>8s}")
        for pt in r["error_rates"]:
            p = pt["p"]
            ler = pt["logical_error_rate"]
            k = r["k"]
            p_l = 1 - (1 - ler) ** (1 / k) if ler > 0 else 0
            uncoded = 1 - (1 - p) ** k
            print(f"  {p:6.4f}  {ler:8.5f}  {p_l:8.5f}  {uncoded:8.5f}")

    # Save
    output = Path("results/threshold_simulation_missing.json")
    output.parent.mkdir(parents=True, exist_ok=True)
    with open(output, "w") as f:
        json.dump(all_results, f, indent=2)
    print(f"\nResults saved to {output}")


if __name__ == "__main__":
    main()
