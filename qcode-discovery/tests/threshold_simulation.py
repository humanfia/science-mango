"""Code-capacity threshold simulation for headline BB codes.

Simulates independent bit-flip noise (the *code capacity* noise model,
not the phenomenological model -- phenomenological noise additionally
includes measurement errors over multiple syndrome-extraction rounds,
which this script does not model):

- Apply random X errors to each qubit with probability p
- Compute Z syndrome
- Decode with BP-OSD (OSD-CS order 7)
- Check if residual error is a nontrivial logical operator

This is the simplest noise model and provides a code-capacity
threshold estimate.
"""

import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.sparse import csr_matrix

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code
from ldpc import BpOsdDecoder


CODES_ORIGINAL = [
    {
        "label": "[[144,12,12]] gross code",
        "ell": 12, "m": 6,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
    },
    {
        "label": "[[144,32,2]] A=B (Theorem 1: d=2)",
        "ell": 12, "m": 6,
        "A_terms": [(4, 0), (0, 0), (0, 2)],
        "B_terms": [(0, 2), (0, 0), (4, 0)],
    },
    {
        "label": "[[288,32,4]] (MILP d=4)",
        "ell": 24, "m": 6,
        "A_terms": [(12, 0), (0, 2), (0, 4)],
        "B_terms": [(0, 3), (10, 0), (20, 0)],
    },
    {
        "label": "[[360,40,2]] (MILP d=2)",
        "ell": 15, "m": 12,
        "A_terms": [(0, 0), (0, 10), (0, 11)],
        "B_terms": [(0, 0), (5, 0), (10, 0)],
    },
]

# MILP-confirmed best codes for new simulations
CODES_MILP = [
    {
        "label": "[[144,12,12]] gross code (control)",
        "ell": 12, "m": 6,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
    },
    {
        "label": "[[288,24,12]] MILP d=12, FOM=12.0",
        "ell": 12, "m": 12,
        "A_terms": [(6, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (2, 0), (4, 0)],
    },
    {
        "label": "[[288,16,12]] MILP d=12, FOM=8.0",
        "ell": 12, "m": 12,
        "A_terms": [(0, 1), (0, 2), (3, 0)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
    },
    {
        "label": "[[144,24,6]] MILP d=6, FOM=6.0",
        "ell": 12, "m": 6,
        "A_terms": [(6, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (2, 0), (4, 0)],
    },
    {
        "label": "[[360,16,14]] MILP d=14, FOM=8.7",
        "ell": 15, "m": 12,
        "A_terms": [(0, 2), (0, 4), (3, 0)],
        "B_terms": [(0, 6), (2, 0), (4, 0)],
    },
    {
        "label": "[[360,20,<=14]] MILP d<=14, FOM<=10.9 (C4)",
        "ell": 30, "m": 6,
        "A_terms": [(0, 0), (3, 4), (6, 2), (1, 0)],
        "B_terms": [(0, 0), (3, 2), (6, 4), (0, 2)],
    },
]

CODES = CODES_MILP  # Default to MILP-confirmed codes

ERROR_RATES = [0.002, 0.005, 0.008, 0.01, 0.015, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08]
NUM_SHOTS = 100_000


def run_threshold_simulation(code_spec, error_rates, num_shots, verbose=True):
    """Run code capacity threshold simulation for a single code."""
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

    # H_Z matrix (detects X errors)
    hz = np.array(code.matrix_z, dtype=np.uint8)
    hz_sparse = csr_matrix(hz)

    # Logical Z operators: Z-part (for checking X-error residuals)
    logicals = np.array(code.get_logical_ops(), dtype=np.uint8)
    log_z_zpart = logicals[k:, n:]  # k × n binary matrix

    # Build BP-OSD decoder
    decoder = BpOsdDecoder(
        hz_sparse,
        error_rate=0.01,  # initial; updated per p
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

        results.append({
            "p": p,
            "logical_error_rate": ler,
            "logical_errors": logical_errors,
            "num_shots": num_shots,
            "time_s": round(elapsed, 1),
        })

        if verbose:
            print(f"  p={p:.4f}  LER={ler:.5f}  ({logical_errors:5d}/{num_shots})  [{elapsed:.1f}s]")

    total_time = time.time() - t0

    if verbose:
        print(f"  Total: {total_time:.0f}s ({total_time/60:.1f} min)")

    return {
        "label": label,
        "n": n,
        "k": k,
        "ell": code_spec["ell"],
        "m": code_spec["m"],
        "error_rates": results,
        "total_time_s": round(total_time, 1),
    }


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--codes", choices=["milp", "original", "all"], default="milp",
                        help="Which code set to simulate")
    args = parser.parse_args()

    if args.codes == "milp":
        codes = CODES_MILP
        output_file = "results/threshold_simulation_milp.json"
    elif args.codes == "original":
        codes = CODES_ORIGINAL
        output_file = "results/threshold_simulation_original.json"
    else:
        codes = CODES_MILP + CODES_ORIGINAL
        output_file = "results/threshold_simulation_all.json"

    print("Code Capacity Threshold Simulation")
    print(f"Codes: {len(codes)} ({args.codes})")
    print(f"Error rates: {ERROR_RATES}")
    print(f"Shots per rate: {NUM_SHOTS:,}")

    np.random.seed(42)

    all_results = []
    t_start = time.time()

    for code_spec in codes:
        result = run_threshold_simulation(
            code_spec, ERROR_RATES, NUM_SHOTS, verbose=True
        )
        all_results.append(result)

    total = time.time() - t_start

    # Summary table
    print(f"\n{'=' * 70}")
    print(f"SUMMARY ({total/60:.1f} minutes total)")
    print(f"{'=' * 70}")
    header = f"{'Code':45s}"
    for p in ERROR_RATES:
        header += f"  {p:.3f}"
    print(header)
    print("-" * len(header))

    for r in all_results:
        row = f"{r['label']:45s}"
        for pt in r["error_rates"]:
            ler = pt["logical_error_rate"]
            row += f"  {ler:.3f}"
        print(row)

    # Save
    output = Path(output_file)
    output.parent.mkdir(parents=True, exist_ok=True)
    with open(output, "w") as f:
        json.dump(all_results, f, indent=2)
    print(f"\nResults saved to {output}")


if __name__ == "__main__":
    main()
