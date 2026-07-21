"""Depolarizing-channel simulation for non-CSS PBB codes, decoded with
an iid X/Z BP-OSD prior.

Errors are sampled from the true single-qubit depolarizing channel:
each qubit independently gets X, Y, or Z with probability p/3.  The
resulting syndrome is then decoded with BP-OSD configured to treat the
X-part and Z-part of the symplectic error vector as **independent**
bit-flip channels (each with marginal rate 2p/3).  That prior is
mismatched with respect to the channel: under depolarizing noise the
X-part and Z-part of e are correlated through Y errors (which flip
both bits simultaneously), and BP-OSD with iid bit priors does not
model that correlation.

What this means for the reported numbers:

* The threshold reported here is **not** the optimal depolarizing
  threshold of these codes.  It is the threshold attainable under this
  specific decoder configuration; an optimal correlated decoder (e.g.,
  quaternary BP over GF(4), or a joint X/Z BP-OSD with a 4-symbol
  channel model) would do at least as well, possibly better.  Treat
  the values as a lower bound on the depolarizing threshold under an
  optimal decoder, not as the depolarizing threshold itself.
* The noise model in the sampler is genuinely depolarizing -- the
  mismatch is purely on the decoder side.
* The output JSON path is preserved as
  ``results/threshold_simulation_depolarizing.json`` for compatibility
  with existing paper figure references; the per-record ``noise_model``
  field is likewise still ``"depolarizing"`` (the noise really is
  depolarizing).  The file rename communicates that what is *measured*
  is a decoder-mismatched threshold, not an optimal one.

Usage:
    uv run python tests/threshold_simulation_independent_xz.py
    uv run python tests/threshold_simulation_independent_xz.py --shots 100000
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


# Same codes as threshold_simulation_noncss.py.
# C/D values follow paper.tex Table V (post-`migrate_cd_convention.py` convention),
# matching the canonical catalog records in `results/campaign7_publication_merged.jsonl`.
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


def run_simulation_depolarizing(code_spec, error_rates, num_shots, verbose=True):
    """Run depolarizing noise simulation for a single (possibly non-CSS) code.

    Under depolarizing noise at rate p, each qubit independently gets:
    - X error with probability p/3
    - Y error (= XZ) with probability p/3
    - Z error with probability p/3
    - No error with probability 1-p

    The full symplectic error vector is (e_x | e_z) of length 2n.
    The syndrome is H @ (e_x | e_z)^T mod 2 using the full stabilizer matrix.
    """
    label = code_spec["label"]

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
        print(f"  {'CSS' if is_css else 'non-CSS'}  |  DEPOLARIZING  |  {len(error_rates)} rates × {num_shots} shots")
        print(f"{'=' * 60}")

    # qldpc stores stabilizers as [H_x | H_z] in symplectic form.
    # The syndrome is the symplectic inner product: s = H_x · e_z + H_z · e_x.
    # For the ldpc decoder (which computes M @ e), we need the column-swapped
    # matrix M = [H_z | H_x] so that M @ (e_x | e_z) = H_z · e_x + H_x · e_z.
    stab = np.array(code.matrix, dtype=np.uint8) % 2
    h_x = stab[:, :n]   # X-part of stabilizers
    h_z = stab[:, n:]    # Z-part of stabilizers
    h_symp = np.concatenate([h_z, h_x], axis=1)  # [H_z | H_x]

    # Get symplectic logicals
    if is_css:
        logicals = np.array(code.get_logical_ops(), dtype=np.uint8)
        # logicals: (2k, 2n) -- first k are X logicals, last k are Z logicals
        sym_logicals = logicals
    else:
        sym_logicals = get_symplectic_logicals(code)
        if sym_logicals.shape[0] == 0:
            print(f"  WARNING: no logicals found, skipping")
            return None

    if verbose:
        print(f"  Symplectic check matrix: {h_symp.shape[0]} × {h_symp.shape[1]}")
        print(f"  Logical operators: {sym_logicals.shape[0]}")

    h_sparse = csr_matrix(h_symp)

    # Channel probs for BP-OSD: each of the 2n columns corresponds to
    # either an e_x or e_z component, each with marginal prob 2p/3.
    decoder = BpOsdDecoder(
        h_sparse,
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
        # Channel probs for the 2n-column check matrix
        # Each of the 2n columns sees errors at rate related to p
        # X-part columns: P(e_x=1) = P(X) + P(Y) = p/3 + p/3 = 2p/3
        # Z-part columns: P(e_z=1) = P(Y) + P(Z) = p/3 + p/3 = 2p/3
        p_eff = 2 * p / 3
        decoder.update_channel_probs(np.full(2 * n, p_eff))

        logical_errors = 0
        for _ in range(num_shots):
            # Generate depolarizing errors
            # For each qubit, draw which Pauli error (if any) occurs
            r = np.random.random(n)
            e_x = np.zeros(n, dtype=np.uint8)
            e_z = np.zeros(n, dtype=np.uint8)

            # X error: r in [0, p/3)
            x_mask = r < (p / 3)
            e_x[x_mask] = 1

            # Y error (= XZ): r in [p/3, 2p/3)
            y_mask = (r >= p / 3) & (r < 2 * p / 3)
            e_x[y_mask] = 1
            e_z[y_mask] = 1

            # Z error: r in [2p/3, p)
            z_mask = (r >= 2 * p / 3) & (r < p)
            e_z[z_mask] = 1

            # Full symplectic error vector
            error = np.concatenate([e_x, e_z])

            # Syndrome (symplectic): h_symp @ e = H_z·e_x + H_x·e_z
            syndrome = (h_symp @ error) % 2

            # Decode
            correction = decoder.decode(syndrome)
            residual = (error + correction) % 2

            # Check if residual anticommutes with any logical operator
            # Symplectic inner product: <l, r> = l_x · r_z + l_z · r_x
            for i in range(sym_logicals.shape[0]):
                l = sym_logicals[i]
                l_x = l[:n]
                l_z = l[n:]
                r_x = residual[:n]
                r_z = residual[n:]
                sip = (np.dot(l_x, r_z) + np.dot(l_z, r_x)) % 2
                if sip:
                    logical_errors += 1
                    break

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
        "is_css": is_css,
        "noise_model": "depolarizing",
        "error_rates": results,
        "total_time_s": round(total_time, 1),
    }


def main():
    import argparse
    parser = argparse.ArgumentParser(
        description="Depolarizing channel + iid X/Z BP-OSD prior -- see module docstring."
    )
    parser.add_argument("--shots", type=int, default=NUM_SHOTS, help="Shots per error rate")
    parser.add_argument("--no-baseline", action="store_true", help="Skip CSS gross code baseline")
    args = parser.parse_args()

    codes = CODES_PBB[:]
    if not args.no_baseline:
        codes = CODES_CSS_BASELINE + codes

    print("Depolarizing channel + iid X/Z BP-OSD prior -- decoder-mismatched threshold")
    print(f"Codes: {len(codes)}")
    print(f"Error rates: {ERROR_RATES}")
    print(f"Shots per rate: {args.shots:,}")

    np.random.seed(42)

    all_results = []
    t_start = time.time()

    for code_spec in codes:
        result = run_simulation_depolarizing(
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
    output = Path("results/threshold_simulation_depolarizing.json")
    output.parent.mkdir(parents=True, exist_ok=True)
    with open(output, "w") as f:
        json.dump(all_results, f, indent=2)
    print(f"\nResults saved to {output}")


if __name__ == "__main__":
    main()
