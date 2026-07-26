"""Code-capacity LER simulation for the [[360,12,<=24]] PBB code.

Mirrors tests/threshold_simulation_noncss.py protocol exactly (BP-OSD with
product_sum BP, max_iter=20, OSD-CS order 7, code-capacity bit-flip noise),
so the result is directly comparable to the [[360,12,<=20]] data in
results/threshold_simulation_missing.json.

Output: results/threshold_simulation_360_12_24.json (single record).

Usage:
    uv run python tests/threshold_simulation_360_12_24.py --shots 100000  # full
    uv run python tests/threshold_simulation_360_12_24.py --shots 1000     # smoke test
"""
import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.sparse import csr_matrix

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evaluation.pbb_code import build_pbb_code, get_symplectic_logicals
from ldpc import BpOsdDecoder


# Top-FOM TRUSTED PBB at (30,6).  FOM <= 19.20.
CODE = {
    "label": "[[360,12,<=24]] PBB (top TRUSTED FOM)",
    "ell": 30, "m": 6,
    "A_terms": [(1, 2), (4, 3), (4, 4)],
    "B_terms": [(0, 0), (1, 5), (5, 4)],
    "C_terms": [(1, 0), (4, 0)],
    "D_terms": [(1, 2), (4, 2)],
}

ERROR_RATES = [0.002, 0.005, 0.008, 0.01, 0.015, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--shots", type=int, default=100_000)
    ap.add_argument("--out", default="results/threshold_simulation_360_12_24.json")
    ap.add_argument("--seed", type=int, default=42)
    args = ap.parse_args()

    np.random.seed(args.seed)

    code = build_pbb_code(
        CODE["ell"], CODE["m"],
        CODE["A_terms"], CODE["B_terms"],
        CODE["C_terms"], CODE["D_terms"],
    )
    n = code.num_qudits
    k = code.dimension
    print(f"{CODE['label']}  n={n}, k={k}")

    stab = np.array(code.matrix, dtype=np.uint8) % 2
    hz = stab[:, n:]
    sym_logicals = get_symplectic_logicals(code)
    log_z_parts = sym_logicals[:, n:].astype(np.uint8)
    print(f"check matrix: {hz.shape};  logicals: {log_z_parts.shape}")

    decoder = BpOsdDecoder(
        csr_matrix(hz),
        error_rate=0.01,
        bp_method="product_sum",
        max_iter=20,
        osd_method="osd_cs",
        osd_order=7,
    )

    results = []
    t0 = time.time()
    for p in ERROR_RATES:
        t_p = time.time()
        decoder.update_channel_probs(np.full(n, p))
        logical_errors = 0
        for _ in range(args.shots):
            error = (np.random.random(n) < p).astype(np.uint8)
            syndrome = (hz @ error) % 2
            correction = decoder.decode(syndrome)
            residual = (error + correction) % 2
            log_check = (log_z_parts @ residual) % 2
            if np.any(log_check):
                logical_errors += 1
        ler = logical_errors / args.shots
        elapsed = time.time() - t_p
        marker = " ***" if ler > p else ""
        print(f"  p={p:.4f}  LER={ler:.5f}  ({logical_errors}/{args.shots})  [{elapsed:.0f}s]{marker}",
              flush=True)
        results.append({
            "p": p,
            "logical_error_rate": ler,
            "logical_errors": logical_errors,
            "num_shots": args.shots,
            "time_s": round(elapsed, 1),
        })

    total = time.time() - t0
    print(f"\nTotal: {total:.0f}s ({total/60:.1f} min)")

    out = {
        "label": CODE["label"],
        "n": n, "k": k,
        "ell": CODE["ell"], "m": CODE["m"],
        "is_css": False,
        "noise_model": "code_capacity_bit_flip",
        "error_rates": results,
        "total_time_s": round(total, 1),
        "decoder": "BpOsd(product_sum, max_iter=20, osd_cs order 7)",
        "seed": args.seed,
    }
    Path(args.out).write_text(json.dumps(out, indent=2))
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
