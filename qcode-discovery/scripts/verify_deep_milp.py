"""Deep MILP verification -- solve ALL logicals from ALL codes in one pool.

Pushes TRUSTED codes toward EXACT by running every logical as an independent
ILP with long timeouts, fully saturating all available cores.

Output: results/campaign7_deep_milp.jsonl -- appended incrementally per code.

Usage:
    uv run python scripts/verify_deep_milp.py --workers 60 --timeout 3600
    uv run python scripts/verify_deep_milp.py --lattices 9,6 12,6 --timeout 14400
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime, timezone

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from evaluation.distance_milp import ilp_min_weight_symplectic
from evaluation.pbb_code import build_pbb_code, get_symplectic_logicals

INPUT_FILE = "results/campaign7_publication_merged.jsonl"
OUTPUT_FILE = "results/campaign7_deep_milp.jsonl"


def solve_single_logical(args):
    """Solve one logical -- runs in a worker process."""
    stab_matrix, logical_vec, timeout, code_idx, logical_idx = args
    t0 = time.monotonic()
    try:
        w, optimal = ilp_min_weight_symplectic(stab_matrix, logical_vec, timeout=timeout)
        elapsed = time.monotonic() - t0
        return {
            "code_idx": code_idx,
            "logical_idx": logical_idx,
            "weight": w,
            "optimal": optimal,
            "time_s": round(elapsed, 1),
            "error": None,
        }
    except Exception as e:
        elapsed = time.monotonic() - t0
        return {
            "code_idx": code_idx,
            "logical_idx": logical_idx,
            "weight": None,
            "optimal": False,
            "time_s": round(elapsed, 1),
            "error": str(e),
        }


def main():
    parser = argparse.ArgumentParser(description="Deep MILP verification")
    parser.add_argument("--workers", type=int, default=60,
                        help="Total worker processes (default: 60)")
    parser.add_argument("--timeout", type=int, default=3600,
                        help="Timeout per logical (seconds)")
    parser.add_argument("--input", type=str, default=INPUT_FILE)
    parser.add_argument("--output", type=str, default=OUTPUT_FILE)
    parser.add_argument("--lattices", nargs="+", type=str, default=None,
                        help="Filter to specific lattices, e.g. 9,6 12,6")
    parser.add_argument("--min-fom", type=float, default=5.0,
                        help="Only verify codes with FOM >= this")
    parser.add_argument("--rerun-partial", action="store_true",
                        help="Re-run codes that finished as partial (not EXACT)")
    parser.add_argument("--bliss-hashes-file", type=str, default=None,
                        help="Path to a JSON or text file restricting work to the listed bliss_hashes. "
                             "JSON: a list of hashes, or an object with a 'codes' array of {bliss_hash}. "
                             "Text: one hash per line, # for comments.")
    args = parser.parse_args()

    # Parse lattice filter
    lat_filter = None
    if args.lattices:
        lat_filter = set()
        for s in args.lattices:
            parts = s.split(",")
            lat_filter.add((int(parts[0]), int(parts[1])))

    # Parse bliss-hash filter
    hash_filter = None
    if args.bliss_hashes_file:
        with open(args.bliss_hashes_file) as f:
            content = f.read().strip()
        hash_filter = set()
        if content.startswith("{") or content.startswith("["):
            data = json.loads(content)
            if isinstance(data, list):
                for entry in data:
                    if isinstance(entry, str):
                        hash_filter.add(entry)
                    elif isinstance(entry, dict) and "bliss_hash" in entry:
                        hash_filter.add(entry["bliss_hash"])
            elif isinstance(data, dict) and "codes" in data:
                for entry in data["codes"]:
                    if "bliss_hash" in entry:
                        hash_filter.add(entry["bliss_hash"])
        else:
            for line in content.splitlines():
                line = line.strip()
                if line and not line.startswith("#"):
                    hash_filter.add(line)
        print(f"  bliss-hash filter: {len(hash_filter)} hashes from {args.bliss_hashes_file}")

    # Load codes
    print(f"Loading codes from {args.input}...")
    all_codes = []
    with open(args.input) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            all_codes.append(json.loads(line))

    # Filter to TRUSTED codes with FOM >= threshold
    trusted = []
    seen = set()
    for c in all_codes:
        if c.get("trust_level") != "TRUSTED":
            continue
        if c.get("fom", 0) < args.min_fom:
            continue
        lat = (c["ell"], c["m"])
        if lat_filter and lat not in lat_filter:
            continue
        if hash_filter is not None and c.get("bliss_hash") not in hash_filter:
            continue
        key = (str(c["A_terms"]), str(c["B_terms"]),
               str(c["C_terms"]), str(c["D_terms"]), c["ell"], c["m"])
        if key in seen:
            continue
        seen.add(key)
        trusted.append(c)

    # Sort by n (smallest first)
    trusted.sort(key=lambda c: (c["n"], -c.get("fom", 0)))

    print(f"  {len(trusted)} TRUSTED codes with FOM >= {args.min_fom}")
    for lat in sorted(set((c["ell"], c["m"]) for c in trusted)):
        lat_codes = [c for c in trusted if (c["ell"], c["m"]) == lat]
        print(f"    ({lat[0]},{lat[1]}): {len(lat_codes)} codes")

    # Load already-verified codes (for resume)
    done_keys = set()
    partial_records = {}  # key -> record (for rerun-partial with per-logical data)
    if os.path.exists(args.output):
        with open(args.output) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                r = json.loads(line)
                key = (str(r["A_terms"]), str(r["B_terms"]),
                       str(r["C_terms"]), str(r["D_terms"]), r["ell"], r["m"])
                done_keys.add(key)
                if args.rerun_partial and not r.get("milp_exact_deep", False):
                    partial_records[key] = r
        if args.rerun_partial:
            print(f"  Resuming: {len(done_keys)} already verified, "
                  f"{len(partial_records)} partial (will re-run unsolved logicals)")
            done_keys -= set(partial_records.keys())
        else:
            print(f"  Resuming: {len(done_keys)} already verified")

    todo = []
    for c in trusted:
        key = (str(c["A_terms"]), str(c["B_terms"]),
               str(c["C_terms"]), str(c["D_terms"]), c["ell"], c["m"])
        if key not in done_keys:
            todo.append(c)

    # Prepare tasks -- for partial reruns, only submit unsolved logicals
    print(f"\nPreparing logicals for {len(todo)} codes...")
    all_tasks = []       # (stab_matrix, logical_vec, timeout, code_idx, logical_idx)
    code_metadata = []   # parallel list indexed by code_idx
    total_logicals = 0
    skipped_logicals = 0

    # Pre-populate code_results with previously solved logicals
    code_results = defaultdict(dict)

    for ci, c in enumerate(todo):
        ell = c["ell"]
        m = c["m"]
        A = [tuple(t) for t in c["A_terms"]]
        B = [tuple(t) for t in c["B_terms"]]
        C = [tuple(t) for t in c["C_terms"]]
        D = [tuple(t) for t in c["D_terms"]]

        code = build_pbb_code(ell, m, A, B, C, D)
        n = code.num_qudits
        k = code.dimension

        stab_matrix = np.array(code.matrix, dtype=int) % 2
        logicals = get_symplectic_logicals(code)
        num_logicals = logicals.shape[0]

        code_metadata.append({
            "entry": c,
            "n": n,
            "k": k,
            "num_logicals": num_logicals,
            "code_idx": ci,
        })

        # Check for previous per-logical results
        key = (str(c["A_terms"]), str(c["B_terms"]),
               str(c["C_terms"]), str(c["D_terms"]), c["ell"], c["m"])
        prev = partial_records.get(key)
        prev_logicals = prev.get("per_logical", []) if prev else []

        for li in range(num_logicals):
            # Skip logicals already solved optimally in a previous run
            if li < len(prev_logicals) and prev_logicals[li].get("opt", False):
                code_results[ci][li] = {
                    "code_idx": ci,
                    "logical_idx": li,
                    "weight": prev_logicals[li]["w"],
                    "optimal": True,
                    "time_s": prev_logicals[li].get("t", 0),
                    "error": None,
                }
                skipped_logicals += 1
            else:
                all_tasks.append((stab_matrix, logicals[li], args.timeout, ci, li))
                total_logicals += 1

    print(f"  Total logicals to solve: {total_logicals}")
    if skipped_logicals:
        print(f"  Skipped (already optimal): {skipped_logicals}")
    print(f"  Workers: {args.workers}, Timeout/logical: {args.timeout}s")
    print(f"  All logicals submitted to a single pool -- full core saturation\n")

    header = (f"{'#':>3} {'lattice':>8} {'n':>4} {'k':>3} {'old_d':>5} "
              f"{'new_d':>5} {'FOM':>8} {'solved':>8} {'status':>8} {'time':>8}")
    print(header)
    print("-" * 75)
    sys.stdout.flush()

    # Submit everything to one pool
    code_start_times = {}
    codes_done = set()
    pushed_to_exact = 0
    improved = 0
    output_order = 0

    t_global = time.monotonic()

    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = {}
        for task in all_tasks:
            ci = task[3]
            if ci not in code_start_times:
                code_start_times[ci] = time.monotonic()
            f = pool.submit(solve_single_logical, task)
            futures[f] = (task[3], task[4])  # (code_idx, logical_idx)

        for future in as_completed(futures):
            ci, li = futures[future]
            try:
                result = future.result()
            except Exception as e:
                result = {
                    "code_idx": ci, "logical_idx": li,
                    "weight": None, "optimal": False,
                    "time_s": 0, "error": str(e),
                }

            code_results[ci][li] = result

            # Check if this code is complete
            meta = code_metadata[ci]
            if ci not in codes_done and len(code_results[ci]) == meta["num_logicals"]:
                codes_done.add(ci)
                elapsed = time.monotonic() - code_start_times[ci]

                # Analyze
                c = meta["entry"]
                n = meta["n"]
                k = meta["k"]
                old_d = c["d"]
                num_log = meta["num_logicals"]

                d_best = n
                all_optimal = True
                logicals_optimal = 0
                logicals_incumbent = 0
                logicals_failed = 0
                any_found = False
                per_logical_detail = []

                for idx in range(num_log):
                    r = code_results[ci].get(idx)
                    if r is None:
                        logicals_failed += 1
                        all_optimal = False
                        per_logical_detail.append({"w": None, "opt": False})
                        continue
                    w = r["weight"]
                    opt = r["optimal"]
                    per_logical_detail.append({"w": w, "opt": opt, "t": r["time_s"]})
                    if w is not None:
                        d_best = min(d_best, w)
                        any_found = True
                        if opt:
                            logicals_optimal += 1
                        else:
                            logicals_incumbent += 1
                            all_optimal = False
                    else:
                        logicals_failed += 1
                        all_optimal = False

                exact = all_optimal and any_found
                new_d = d_best if any_found else old_d
                new_fom = round(k * new_d * new_d / n, 4) if n > 0 and k > 0 else 0

                if exact:
                    pushed_to_exact += 1
                if new_d != old_d:
                    improved += 1

                status = "EXACT" if exact else "partial"
                marker = " ***" if exact else (" !" if new_d != old_d else "")
                solved_str = f"{logicals_optimal}/{num_log}"
                lat_str = f"({c['ell']},{c['m']})"

                output_order += 1
                print(f"{output_order:3d} {lat_str:>8} {n:4d} {k:3d} {old_d:5d} "
                      f"{new_d:5d} {new_fom:8.2f} {solved_str:>8} {status:>8} "
                      f"{elapsed:7.0f}s{marker}")
                sys.stdout.flush()

                # Write result immediately
                deep_method = "deep_milp" if new_d < old_d or exact else c.get("d_method", "deep_milp")
                out_record = {
                    **{kk: v for kk, v in c.items() if kk != "per_logical"},
                    "d": new_d,
                    "d_method": deep_method,
                    "d_is_exact": exact,
                    "d_is_upper_bound": not exact,
                    "fom": new_fom,
                    "trust_level": "EXACT" if exact else c.get("trust_level", "TRUSTED"),
                    "publication_quality": exact,
                    "d_deep_milp": new_d,
                    "d_original": old_d,
                    "fom_deep": new_fom,
                    "milp_exact_deep": exact,
                    "per_logical": per_logical_detail,
                    "logicals_optimal": logicals_optimal,
                    "logicals_incumbent": logicals_incumbent,
                    "logicals_failed": logicals_failed,
                    "total_logicals": num_log,
                    "deep_milp_time_s": round(elapsed, 1),
                    "timeout_per_logical": args.timeout,
                    "verified_at": datetime.now(timezone.utc).isoformat(),
                }
                with open(args.output, "a") as f:
                    f.write(json.dumps(out_record) + "\n")

    total_elapsed = time.monotonic() - t_global
    print()
    print(f"Done in {total_elapsed/60:.1f} min.")
    print(f"  Pushed to EXACT: {pushed_to_exact}")
    print(f"  Distance changed: {improved}")
    print(f"  Results in {args.output}")


if __name__ == "__main__":
    main()
