"""Intensive BP-OSD search for low-weight codewords on MILP-incumbent codes.

Runs massive trial counts across 3 decoder configurations to either:
- Find a lower-weight codeword (tightening the distance upper bound), or
- Build confidence that the MILP incumbent is close to the true distance.

(Renamed from bp_osd_attack.py -- the old name read like a cryptographic
attack; this is just an aggressive distance-refinement search.  The
output JSON path is preserved as ``results/bp_osd_attack.json`` for
compatibility with existing paper figure references.)

Usage:
    uv run python tests/bp_osd_intensive_search.py                    # both codes, 300k trials
    uv run python tests/bp_osd_intensive_search.py --trials 10000     # quick test
    uv run python tests/bp_osd_intensive_search.py --batches 20       # more batches
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path

from qldpc.objects import Pauli

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code
from evaluation.evaluator import compute_fom

# The two FOM>12 incumbent codes from Campaign 4 re-verification
TARGET_CODES = [
    {
        "label": "[[360,8,≤32]] C4-top1",
        "ell": 30, "m": 6,
        "A_terms": [[9, 0], [0, 1], [0, 2], [3, 1]],
        "B_terms": [[0, 3], [25, 0], [26, 0]],
        "milp_d": 32,
        "milp_fom": 22.76,
        "notes": "4-term A, MILP incumbent 0/16 optimal after 48000s",
    },
    {
        "label": "[[360,12,≤24]] C4-top2",
        "ell": 30, "m": 6,
        "A_terms": [[9, 0], [0, 1], [0, 2]],
        "B_terms": [[0, 3], [25, 0], [26, 0]],
        "milp_d": 24,
        "milp_fom": 19.20,
        "notes": "trinomial, MILP incumbent 0/24 optimal after 72000s",
    },
]

# Multi-decoder configs -- same as soak_test.py plus higher OSD orders
DECODER_CONFIGS = [
    {
        "name": "OSD_0/product_sum",
        "kwargs": {"bp_method": "product_sum"},
    },
    {
        "name": "OSD_CS10/product_sum",
        "kwargs": {
            "bp_method": "product_sum",
            "osd_method": "osd_cs",
            "osd_order": 10,
        },
    },
    {
        "name": "OSD_CS10/minimum_sum",
        "kwargs": {
            "bp_method": "minimum_sum",
            "osd_method": "osd_cs",
            "osd_order": 10,
        },
    },
]


def estimate_distance_with_config(code, num_trials: int, decoder_kwargs: dict) -> tuple[int, int, int]:
    """Returns (d, d_x, d_z) -- min and both components.

    Raises:
        ValueError: if the code has dimension 0 (no logical operators ⇒
            distance undefined; returning 0 would silently corrupt minima).
    """
    if code.dimension == 0:
        raise ValueError(
            "Distance is undefined for k=0 stabilizer codes; "
            "filter k=0 codes upstream."
        )

    trials_x = num_trials // 2
    trials_z = (num_trials + 1) // 2
    d_x = code.get_distance_bound_with_decoder(
        Pauli.X, trials_x, **decoder_kwargs
    )
    d_z = code.get_distance_bound_with_decoder(
        Pauli.Z, trials_z, **decoder_kwargs
    )
    d_x = int(d_x) if d_x == d_x else 999
    d_z = int(d_z) if d_z == d_z else 999
    return min(d_x, d_z), d_x, d_z


def attack_code(
    code_spec: dict,
    num_batches: int = 10,
    trials_per_batch: int = 10000,
) -> dict:
    """Run aggressive BP-OSD attack on a single code."""
    label = code_spec["label"]
    code = build_bb_code(
        code_spec["ell"], code_spec["m"],
        code_spec["A_terms"], code_spec["B_terms"],
    )
    n = code.num_qudits
    k = code.dimension
    milp_d = code_spec["milp_d"]

    num_configs = len(DECODER_CONFIGS)
    total_trials = num_batches * num_configs * trials_per_batch

    print(f"\n{'='*70}")
    print(f"  BP-OSD ATTACK: {label}")
    print(f"  n={n}, k={k}, MILP incumbent d≤{milp_d}, FOM={code_spec['milp_fom']:.2f}")
    print(f"  {num_configs} decoders x {num_batches} batches x {trials_per_batch} trials = {total_trials:,} total")
    print(f"{'='*70}")

    d_global_min = milp_d  # start from MILP incumbent
    d_global_min_x = 999
    d_global_min_z = 999
    all_results = []
    t0 = time.time()

    for cfg in DECODER_CONFIGS:
        cfg_name = cfg["name"]
        cfg_kwargs = cfg["kwargs"]
        print(f"\n  --- {cfg_name} ---")

        for i in range(num_batches):
            t_batch = time.time()
            d, d_x, d_z = estimate_distance_with_config(code, trials_per_batch, cfg_kwargs)
            elapsed = time.time() - t_batch

            improved = d < d_global_min
            if d < d_global_min:
                d_global_min = d
            d_global_min_x = min(d_global_min_x, d_x)
            d_global_min_z = min(d_global_min_z, d_z)

            all_results.append({
                "decoder": cfg_name,
                "batch": i + 1,
                "d": d,
                "d_x": d_x,
                "d_z": d_z,
            })

            marker = ""
            if improved:
                marker = f" *** BEAT MILP! d={d} < {milp_d} ***"
            elif d == d_global_min and d < milp_d:
                marker = f" (matches best BP-OSD d={d})"

            print(f"  Batch {i+1:2d}/{num_batches}: d={d:3d} (X={d_x:3d} Z={d_z:3d})  "
                  f"global_min={d_global_min}  [{elapsed:.1f}s]{marker}")

            sys.stdout.flush()

    total_time = time.time() - t0

    # Summary
    fom_bp = compute_fom(n, k, d_global_min)
    print(f"\n  {'='*60}")
    print(f"  RESULT: BP-OSD best d ≤ {d_global_min}  (MILP had d ≤ {milp_d})")
    print(f"          d_x ≤ {d_global_min_x}, d_z ≤ {d_global_min_z}")
    if d_global_min < milp_d:
        print(f"  *** BP-OSD FOUND TIGHTER BOUND! d: {milp_d} -> {d_global_min} ***")
        print(f"  *** FOM: {code_spec['milp_fom']:.2f} -> {fom_bp:.2f} ***")
        above12 = "YES" if fom_bp > 12 else "NO"
        print(f"  *** Still FOM > 12? {above12} ***")
    else:
        print(f"  BP-OSD could not beat MILP incumbent d={milp_d}")
        print(f"  This INCREASES confidence that d={milp_d} may be correct")
    print(f"  d/sqrt(n) = {d_global_min / math.sqrt(n):.3f}")
    print(f"  Total time: {total_time:.1f}s ({total_time/60:.1f} min)")
    print(f"  Total trials: {total_trials:,}")

    return {
        "label": label,
        "ell": code_spec["ell"],
        "m": code_spec["m"],
        "A_terms": code_spec["A_terms"],
        "B_terms": code_spec["B_terms"],
        "n": n,
        "k": k,
        "milp_d": milp_d,
        "bp_osd_d": d_global_min,
        "bp_osd_d_x": d_global_min_x,
        "bp_osd_d_z": d_global_min_z,
        "fom_milp": code_spec["milp_fom"],
        "fom_bp_osd": fom_bp,
        "beat_milp": d_global_min < milp_d,
        "total_trials": total_trials,
        "total_time_s": total_time,
        "batch_results": all_results,
    }


def main():
    parser = argparse.ArgumentParser(description="BP-OSD attack on Campaign 4 incumbent codes")
    parser.add_argument("--batches", type=int, default=10,
                        help="Batches per decoder config (default: 10)")
    parser.add_argument("--trials", type=int, default=10000,
                        help="Trials per batch (default: 10000)")
    parser.add_argument("--code", type=int, choices=[0, 1],
                        help="Attack only code 0 or 1 (default: both)")
    parser.add_argument("--output", type=str, default="results/bp_osd_attack.json",
                        help="Output JSON file")
    args = parser.parse_args()

    codes = TARGET_CODES if args.code is None else [TARGET_CODES[args.code]]

    print(f"BP-OSD Attack: {len(codes)} codes")
    print(f"Config: {len(DECODER_CONFIGS)} decoders x {args.batches} batches x {args.trials} trials")
    print(f"Total trials per code: {len(DECODER_CONFIGS) * args.batches * args.trials:,}")

    results = []
    for spec in codes:
        result = attack_code(spec, num_batches=args.batches, trials_per_batch=args.trials)
        results.append(result)

    # Final summary
    print(f"\n{'='*70}")
    print(f"  FINAL SUMMARY")
    print(f"{'='*70}")
    for r in results:
        status = "BEAT MILP" if r["beat_milp"] else "MILP HOLDS"
        print(f"  {r['label']}")
        print(f"    MILP d≤{r['milp_d']} -> BP-OSD d≤{r['bp_osd_d']}  [{status}]")
        print(f"    FOM: {r['fom_milp']:.2f} -> {r['fom_bp_osd']:.2f}")
        if r["fom_bp_osd"] > 12:
            print(f"    *** FOM > 12 ***")
        print()

    # Save
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"Results saved to {output_path}")


if __name__ == "__main__":
    main()
