"""Depolarizing-channel LER simulation for the [[360,12,<=20]] PBB code.

Mirrors tests/threshold_simulation_independent_xz.py protocol exactly
(BP-OSD with iid X/Z bit-flip prior, max_iter=20, OSD-CS order 7;
true depolarizing-channel sampler), so the result is directly
comparable to results/threshold_simulation_360_12_24_depol.json which
holds the same data for [[360,12,<=24]].

Output: results/threshold_simulation_360_12_20_depol.json (single record).

Usage:
    uv run python tests/threshold_simulation_360_12_20_depol.py --shots 100000  # full
    uv run python tests/threshold_simulation_360_12_20_depol.py --shots 1000     # smoke
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


# Catalog: code_id 30_6_0260, bliss_hash 5012d8bafff7fd2b
# C/D values follow paper.tex Table V (post-`migrate_cd_convention.py`).
# Label matches the JSON renamed from results/threshold_simulation_360_12_depol.json,
# so re-running this script reproduces the canonical record byte-for-byte.
CODE = {
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
}

ERROR_RATES = [0.002, 0.005, 0.008, 0.01, 0.015, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--shots", type=int, default=100_000)
    ap.add_argument("--out",
                    default="results/threshold_simulation_360_12_20_depol.json")
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
    h_x = stab[:, :n]
    h_z = stab[:, n:]
    h_symp = np.concatenate([h_z, h_x], axis=1)
    sym_logicals = get_symplectic_logicals(code)
    print(f"check matrix: {h_symp.shape};  logicals: {sym_logicals.shape}")

    decoder = BpOsdDecoder(
        csr_matrix(h_symp),
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
        p_eff = 2 * p / 3
        decoder.update_channel_probs(np.full(2 * n, p_eff))

        logical_errors = 0
        for _ in range(args.shots):
            r = np.random.random(n)
            e_x = np.zeros(n, dtype=np.uint8)
            e_z = np.zeros(n, dtype=np.uint8)
            x_mask = r < (p / 3)
            e_x[x_mask] = 1
            y_mask = (r >= p / 3) & (r < 2 * p / 3)
            e_x[y_mask] = 1
            e_z[y_mask] = 1
            z_mask = (r >= 2 * p / 3) & (r < p)
            e_z[z_mask] = 1
            error = np.concatenate([e_x, e_z])
            syndrome = (h_symp @ error) % 2
            correction = decoder.decode(syndrome)
            residual = (error + correction) % 2

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
        "noise_model": "depolarizing",
        "decoder_prior": "iid bit-flip (mismatched; lower bound on optimal threshold)",
        "error_rates": results,
        "total_time_s": round(total, 1),
        "decoder": "BpOsd(product_sum, max_iter=20, osd_cs order 7) on symplectic [H_z | H_x]",
        "seed": args.seed,
    }
    Path(args.out).write_text(json.dumps(out, indent=2))
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
