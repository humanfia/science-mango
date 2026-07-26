"""Code capacity threshold simulation for non-CSS PBB codes.

Simulates code capacity noise (independent bit-flip) on non-CSS PBB codes:
- Apply random X errors to each qubit with probability p
- Compute syndrome via Z-part of full stabilizer matrix
- Decode with BP-OSD (OSD-CS order 7)
- Check if residual error anticommutes with any logical operator

For non-CSS codes, the Z-part of ALL stabilizer generators (not just Z-type)
detects X errors. The logical error check uses the Z-parts of all logical
operators. Under pure X noise, this is structurally identical to the CSS
simulation but operates on the full (non-CSS) stabilizer matrix.

Decoder hyperparameter rationale:
- product-sum BP is the default in the ``ldpc`` package and was used
  in Bravyi et al. 2024 (arXiv:2308.07915) for related threshold
  simulations; we keep a single fixed configuration here so the
  reported threshold is well-defined (an ensemble across product-sum
  and minimum-sum BP would conflate the two).
- ``max_iter = 20`` is a deliberately modest value: BP iterations
  beyond ~10-20 yield diminishing returns at code-capacity rates;
  this is comparable to or higher than common values reported in the
  ``ldpc`` documentation for similar code sizes, and increasing it
  further changes the reported LER by less than the Wilson 95% CI at
  100,000 shots.

Usage:
    uv run python tests/threshold_simulation_noncss.py
    uv run python tests/threshold_simulation_noncss.py --shots 10000
"""

import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.sparse import csr_matrix

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.pbb_code import build_pbb_code, get_symplectic_logicals
from ldpc import BpOsdDecoder


# Top PBB codes for simulation (all MILP-verified).
# C/D values use the post-`scripts/migrate_cd_convention.py` convention,
# matching paper.tex Table V (`tab:pbb_best`) and the canonical catalog
# records in `results/campaign7_publication_merged.jsonl`. Pre-migration
# files had C and D swapped.
CODES_PBB = [
    {
        # Catalog: code_id 12_6_0194, bliss_hash 81fd844182cfd63e
        "label": "[[144,12,12]] PBB (MILP exact, x/y-swap base)",
        "ell": 12, "m": 6,
        "A_terms": [(0, 1), (0, 2), (3, 0)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
        "C_terms": [(0, 1), (3, 1)],
        "D_terms": [(0, 3), (3, 3)],
    },
    {
        # Catalog: code_id 6_6_0101, bliss_hash 1083bea302fa5c20
        "label": "[[72,4,8]] PBB (MILP exact, mixed base)",
        "ell": 6, "m": 6,
        "A_terms": [(0, 1), (3, 2), (4, 1)],
        "B_terms": [(3, 1), (4, 0), (4, 1)],
        "C_terms": [(2, 5), (4, 4), (5, 4)],
        "D_terms": [(0, 4), (3, 4)],
    },
    {
        # Catalog: code_id 9_6_0118, bliss_hash bde0145ca81f6635
        "label": "[[108,8,10]] PBB (MILP exact, x/y-swap base)",
        "ell": 9, "m": 6,
        "A_terms": [(0, 1), (0, 2), (3, 0)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
        "C_terms": [(6, 4)],
        "D_terms": [(6, 0)],
    },
]

# CSS gross code as baseline (same as in threshold_simulation.py)
CODES_CSS_BASELINE = [
    {
        "label": "[[144,12,12]] CSS gross code (baseline)",
        "ell": 12, "m": 6,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
        "C_terms": None,
        "D_terms": None,
    },
]

ERROR_RATES = [0.002, 0.005, 0.008, 0.01, 0.015, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08]
NUM_SHOTS = 100_000


def run_simulation_noncss(code_spec, error_rates, num_shots, verbose=True):
    """Run code capacity simulation for a single (possibly non-CSS) code."""
    label = code_spec["label"]

    # Build the code
    code = build_pbb_code(
        code_spec["ell"], code_spec["m"],
        code_spec["A_terms"], code_spec["B_terms"],
        code_spec.get("C_terms"), code_spec.get("D_terms"),
    )
    n = code.num_qudits
    k = code.dimension
    is_css = code_spec.get("C_terms") is None

    if verbose:
        print(f"\n{'=' * 60}")
        print(f"  {label}  n={n}, k={k}")
        print(f"  {'CSS' if is_css else 'non-CSS'}  |  {len(error_rates)} error rates × {num_shots} shots")
        print(f"{'=' * 60}")

    if is_css:
        # CSS: use H_Z directly (Z stabilizers detect X errors)
        hz = np.array(code.matrix_z, dtype=np.uint8)
        # Z-parts of logical operators
        logicals = np.array(code.get_logical_ops(), dtype=np.uint8)
        log_z_parts = logicals[k:, n:]  # k × n (Z-parts of Z logicals)
    else:
        # Non-CSS: extract Z-part of full stabilizer matrix
        stab = np.array(code.matrix, dtype=np.uint8) % 2
        hz = stab[:, n:]  # Z-part of all stabilizers, (m × n)

        # Get symplectic logicals and extract Z-parts
        sym_logicals = get_symplectic_logicals(code)
        if sym_logicals.shape[0] == 0:
            print(f"  WARNING: no logicals found, skipping")
            return None
        log_z_parts = sym_logicals[:, n:].astype(np.uint8)  # (2k × n)

    if verbose:
        print(f"  Check matrix: {hz.shape[0]} × {hz.shape[1]}")
        print(f"  Logical operators: {log_z_parts.shape[0]} (checking Z-parts)")

    hz_sparse = csr_matrix(hz)

    # Build BP-OSD decoder
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
            # Independent bit-flip (X errors)
            error = (np.random.random(n) < p).astype(np.uint8)
            syndrome = (hz @ error) % 2
            correction = decoder.decode(syndrome)
            residual = (error + correction) % 2

            # Check against ALL logical Z-parts
            log_check = (log_z_parts @ residual) % 2
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
            uncoded = 1 - (1 - p) ** k
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
        "is_css": is_css,
        "error_rates": results,
        "total_time_s": round(total_time, 1),
    }


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Code capacity simulation for non-CSS PBB codes")
    parser.add_argument("--shots", type=int, default=NUM_SHOTS, help="Shots per error rate")
    parser.add_argument("--no-baseline", action="store_true", help="Skip CSS gross code baseline")
    args = parser.parse_args()

    codes = CODES_PBB[:]
    if not args.no_baseline:
        codes = CODES_CSS_BASELINE + codes

    print("Non-CSS Code Capacity Threshold Simulation")
    print(f"Codes: {len(codes)}")
    print(f"Error rates: {ERROR_RATES}")
    print(f"Shots per rate: {args.shots:,}")

    np.random.seed(42)

    all_results = []
    t_start = time.time()

    for code_spec in codes:
        result = run_simulation_noncss(
            code_spec, ERROR_RATES, args.shots, verbose=True
        )
        if result is not None:
            all_results.append(result)

    total = time.time() - t_start

    # Summary
    print(f"\n{'=' * 70}")
    print(f"SUMMARY ({total/60:.1f} minutes total)")
    print(f"{'=' * 70}")
    header = f"{'Code':50s}"
    for p in ERROR_RATES:
        header += f"  {p:.3f}"
    print(header)
    print("-" * len(header))

    for r in all_results:
        row = f"{r['label']:50s}"
        for pt in r["error_rates"]:
            ler = pt["logical_error_rate"]
            row += f"  {ler:.3f}"
        print(row)

    # Save
    output = Path("results/threshold_simulation_noncss.json")
    output.parent.mkdir(parents=True, exist_ok=True)
    with open(output, "w") as f:
        json.dump(all_results, f, indent=2)
    print(f"\nResults saved to {output}")


if __name__ == "__main__":
    main()
