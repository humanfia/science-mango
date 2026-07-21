"""Intensive BP-OSD search on FOM 9-12 incumbent codes -- parallel version.

Runs 4 codes in parallel using multiprocessing.

(Renamed from bp_osd_attack_batch2.py.  The output JSON path is
preserved as ``results/bp_osd_attack_batch2.json`` for compatibility
with existing paper figure references.)
"""

from __future__ import annotations

import json
import sys
import time
from multiprocessing import Process, Queue
from pathlib import Path

from qldpc.objects import Pauli

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code
from evaluation.evaluator import compute_fom

TARGET_CODES = [
    {
        "label": "[[288,8,≤20]] FOM=11.11",
        "ell": 24, "m": 6,
        "A_terms": [[0, 0], [1, 4], [14, 1]],
        "B_terms": None,  # filled from JSONL
        "milp_d": 20,
        "milp_fom": 11.11,
    },
    {
        "label": "[[360,20,≤14]] FOM=10.89",
        "ell": 30, "m": 6,
        "A_terms": [[0, 0], [3, 4], [6, 2], [1, 0]],
        "B_terms": None,
        "milp_d": 14,
        "milp_fom": 10.89,
    },
    {
        "label": "[[360,8,≤22]] FOM=10.76",
        "ell": 30, "m": 6,
        "A_terms": [[9, 0], [0, 1], [0, 2], [3, 3]],
        "B_terms": None,
        "milp_d": 22,
        "milp_fom": 10.76,
    },
    {
        "label": "[[288,12,≤16]] FOM=10.67",
        "ell": 24, "m": 6,
        "A_terms": [[1, 0], [0, 0], [0, 1]],
        "B_terms": None,
        "milp_d": 16,
        "milp_fom": 10.67,
    },
]

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


def fill_b_terms():
    """Fill in B_terms from the reverified JSONL."""
    with open("results/campaign4_reverified.jsonl") as f:
        for line in f:
            r = json.loads(line)
            if r["stage"] != "milp_incumbent":
                continue
            for t in TARGET_CODES:
                if t["B_terms"] is not None:
                    continue
                a_match = (
                    sorted(map(tuple, r["A_terms"])) == sorted(map(tuple, t["A_terms"]))
                    and r["d"] == t["milp_d"]
                    and r["n"] == 2 * t["ell"] * t["m"]
                )
                if a_match:
                    t["B_terms"] = r["B_terms"]
                    t["ell"] = r["ell"]
                    t["m"] = r["m"]
                    break


def estimate_distance_with_config(code, num_trials: int, decoder_kwargs: dict) -> tuple[int, int, int]:
    """Raises ValueError for k=0 codes (distance undefined)."""
    if code.dimension == 0:
        raise ValueError(
            "Distance is undefined for k=0 stabilizer codes; "
            "filter k=0 codes upstream."
        )
    trials_x = num_trials // 2
    trials_z = (num_trials + 1) // 2
    d_x = code.get_distance_bound_with_decoder(Pauli.X, trials_x, **decoder_kwargs)
    d_z = code.get_distance_bound_with_decoder(Pauli.Z, trials_z, **decoder_kwargs)
    d_x = int(d_x) if d_x == d_x else 999
    d_z = int(d_z) if d_z == d_z else 999
    return min(d_x, d_z), d_x, d_z


def attack_single_code(code_spec: dict, num_batches: int, trials_per_batch: int, result_queue: Queue):
    """Attack a single code -- runs in subprocess."""
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

    print(f"\n[{label}] Starting: n={n}, k={k}, MILP d≤{milp_d}")
    print(f"[{label}] {num_configs} decoders x {num_batches} batches x {trials_per_batch} trials = {total_trials:,}")
    sys.stdout.flush()

    d_global_min = milp_d
    d_global_min_x = 999
    d_global_min_z = 999
    all_batch_results = []
    t0 = time.time()

    for cfg in DECODER_CONFIGS:
        cfg_name = cfg["name"]
        cfg_kwargs = cfg["kwargs"]

        for i in range(num_batches):
            t_batch = time.time()
            d, d_x, d_z = estimate_distance_with_config(code, trials_per_batch, cfg_kwargs)
            elapsed = time.time() - t_batch

            improved = d < d_global_min
            if d < d_global_min:
                d_global_min = d
            d_global_min_x = min(d_global_min_x, d_x)
            d_global_min_z = min(d_global_min_z, d_z)

            all_batch_results.append({
                "decoder": cfg_name, "batch": i + 1,
                "d": d, "d_x": d_x, "d_z": d_z,
            })

            marker = ""
            if improved:
                marker = f" *** BEAT MILP! d={d} < {milp_d} ***"

            print(f"[{label}] {cfg_name} batch {i+1}/{num_batches}: "
                  f"d={d:3d} (X={d_x:3d} Z={d_z:3d}) global_min={d_global_min} [{elapsed:.1f}s]{marker}")
            sys.stdout.flush()

    total_time = time.time() - t0
    fom_bp = compute_fom(n, k, d_global_min)

    print(f"\n[{label}] DONE: BP-OSD d≤{d_global_min} (MILP d≤{milp_d}) "
          f"FOM={fom_bp:.2f} {'BEAT MILP' if d_global_min < milp_d else 'MILP HOLDS'} "
          f"[{total_time/60:.1f} min]")
    sys.stdout.flush()

    result = {
        "label": label,
        "ell": code_spec["ell"],
        "m": code_spec["m"],
        "A_terms": code_spec["A_terms"],
        "B_terms": code_spec["B_terms"],
        "n": n, "k": k,
        "milp_d": milp_d,
        "bp_osd_d": d_global_min,
        "bp_osd_d_x": d_global_min_x,
        "bp_osd_d_z": d_global_min_z,
        "fom_milp": code_spec["milp_fom"],
        "fom_bp_osd": fom_bp,
        "beat_milp": d_global_min < milp_d,
        "total_trials": total_trials,
        "total_time_s": total_time,
        "batch_results": all_batch_results,
    }
    result_queue.put(result)


def main():
    fill_b_terms()

    # Verify all B_terms filled
    for t in TARGET_CODES:
        if t["B_terms"] is None:
            print(f"ERROR: Could not find B_terms for {t['label']}")
            print(f"  A_terms={t['A_terms']}, milp_d={t['milp_d']}")
            sys.exit(1)
        print(f"Found: {t['label']}  A={t['A_terms']}  B={t['B_terms']}")

    num_batches = 10
    trials_per_batch = 10000

    print(f"\nLaunching {len(TARGET_CODES)} parallel BP-OSD attacks")
    print(f"Config: 3 decoders x {num_batches} batches x {trials_per_batch} trials = 300,000 per code")
    print(f"=" * 70)

    result_queue = Queue()
    processes = []
    for spec in TARGET_CODES:
        p = Process(target=attack_single_code, args=(spec, num_batches, trials_per_batch, result_queue))
        p.start()
        processes.append(p)

    for p in processes:
        p.join()

    results = []
    while not result_queue.empty():
        results.append(result_queue.get())

    # Sort by FOM
    results.sort(key=lambda r: -r["fom_bp_osd"])

    print(f"\n{'='*70}")
    print(f"  FINAL SUMMARY -- Batch 2 BP-OSD Attack")
    print(f"{'='*70}")
    for r in results:
        status = "BEAT MILP" if r["beat_milp"] else "MILP HOLDS"
        print(f"  {r['label']}")
        print(f"    MILP d≤{r['milp_d']} -> BP-OSD d≤{r['bp_osd_d']}  [{status}]")
        print(f"    FOM: {r['fom_milp']:.2f} -> {r['fom_bp_osd']:.2f}")
        above = r["fom_bp_osd"] > 12
        print(f"    FOM > 12? {'YES' if above else 'no'}")
        print()

    # Save
    output_path = Path("results/bp_osd_attack_batch2.json")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"Results saved to {output_path}")


if __name__ == "__main__":
    main()
