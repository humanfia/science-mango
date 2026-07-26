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


def load_bliss_hash_filter(path: str) -> list[str]:
    """Load a strict, ordered, non-empty explicit worklist.

    An explicit hash file is an operator-selected verification queue, not a
    second heuristic filter. Malformed or duplicate entries therefore fail
    closed instead of being silently ignored.
    """
    with open(path, encoding="utf-8") as stream:
        content = stream.read().strip()
    if not content:
        raise ValueError("bliss-hash worklist is empty")

    if content.startswith("{") or content.startswith("["):
        data = json.loads(content)
        if isinstance(data, list):
            entries = data
        elif isinstance(data, dict) and isinstance(data.get("codes"), list):
            entries = data["codes"]
        else:
            raise ValueError(
                "JSON worklist must be a list or an object with a 'codes' list"
            )
    else:
        entries = [
            line.strip()
            for line in content.splitlines()
            if line.strip() and not line.lstrip().startswith("#")
        ]

    hashes: list[str] = []
    seen: set[str] = set()
    for index, entry in enumerate(entries):
        if isinstance(entry, str):
            value = entry.strip()
        elif isinstance(entry, dict):
            value = entry.get("bliss_hash")
            value = value.strip() if isinstance(value, str) else ""
        else:
            value = ""
        if not value:
            raise ValueError(
                f"worklist entry {index} must contain a non-empty bliss_hash"
            )
        if value in seen:
            raise ValueError(f"duplicate bliss_hash in worklist: {value}")
        seen.add(value)
        hashes.append(value)
    if not hashes:
        raise ValueError("bliss-hash worklist contains no hashes")
    return hashes


def select_codes_for_verification(
    all_codes,
    *,
    min_fom: float,
    lat_filter=None,
    hash_filter: list[str] | None = None,
):
    """Select unique codes for deep verification.

    Automatic campaigns remain restricted to TRUSTED rows above ``min_fom``.
    A supplied hash worklist is an exact operator allowlist and intentionally
    overrides those two search heuristics, so PARTIAL or low-FOM rows explicitly
    queued for adjudication cannot disappear before MILP. Lattice filters stay
    active and every requested hash must resolve exactly once.
    """
    by_hash = defaultdict(list)
    if hash_filter is not None:
        requested = set(hash_filter)
        for code in all_codes:
            bliss_hash = code.get("bliss_hash")
            if bliss_hash in requested:
                by_hash[bliss_hash].append(code)
        missing = [value for value in hash_filter if not by_hash[value]]
        ambiguous = [value for value in hash_filter if len(by_hash[value]) > 1]
        if missing:
            raise ValueError(
                "requested bliss_hash values were not found: "
                + ", ".join(missing)
            )
        if ambiguous:
            raise ValueError(
                "requested bliss_hash values matched multiple input rows: "
                + ", ".join(ambiguous)
            )
        candidates = [by_hash[value][0] for value in hash_filter]
    else:
        candidates = [
            code for code in all_codes
            if code.get("trust_level") == "TRUSTED"
            and float(code.get("fom", 0) or 0) >= min_fom
        ]

    selected = []
    seen_codes = set()
    for code in candidates:
        bliss_hash = code.get("bliss_hash")
        try:
            lattice = (int(code["ell"]), int(code["m"]))
            key = (
                str(code["A_terms"]),
                str(code["B_terms"]),
                str(code["C_terms"]),
                str(code["D_terms"]),
                lattice[0],
                lattice[1],
            )
        except (KeyError, TypeError, ValueError) as exc:
            if hash_filter is not None:
                raise ValueError(
                    f"explicitly selected code {bliss_hash!r} is malformed: {exc}"
                ) from exc
            continue
        if lat_filter and lattice not in lat_filter:
            if hash_filter is not None:
                raise ValueError(
                    f"explicitly selected code {bliss_hash!r} is excluded by --lattices"
                )
            continue
        if key in seen_codes:
            continue
        seen_codes.add(key)
        selected.append(code)
    return selected


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
    parser.add_argument("--plan-only", action="store_true",
                        help="Validate selection/resume state and print the todo count without "
                             "building codes or launching any MILP solver.")
    parser.add_argument("--rerun-partial", action="store_true",
                        help="Re-run codes that finished as partial (not EXACT)")
    parser.add_argument("--bliss-hashes-file", type=str, default=None,
                        help="Path to a JSON or text file restricting work to the listed bliss_hashes. "
                             "JSON: a list of hashes, or an object with a 'codes' array of {bliss_hash}. "
                             "Text: one hash per line, # for comments. This exact worklist overrides "
                             "the automatic TRUSTED/min-FOM heuristics and fails if any hash is absent.")
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
        try:
            hash_filter = load_bliss_hash_filter(args.bliss_hashes_file)
        except (OSError, json.JSONDecodeError, ValueError) as exc:
            parser.error(f"invalid --bliss-hashes-file: {exc}")
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

    try:
        trusted = select_codes_for_verification(
            all_codes,
            min_fom=args.min_fom,
            lat_filter=lat_filter,
            hash_filter=hash_filter,
        )
    except ValueError as exc:
        parser.error(str(exc))

    # Sort by n (smallest first)
    if hash_filter is None:
        trusted.sort(key=lambda c: (c["n"], -c.get("fom", 0)))

    if hash_filter is None:
        print(f"  {len(trusted)} TRUSTED codes with FOM >= {args.min_fom}")
    else:
        print(f"  {len(trusted)} explicitly selected codes")
    for lat in sorted(set((c["ell"], c["m"]) for c in trusted)):
        lat_codes = [c for c in trusted if (c["ell"], c["m"]) == lat]
        print(f"    ({lat[0]},{lat[1]}): {len(lat_codes)} codes")

    # Load already-verified codes (for resume)
    done_keys = set()
    partial_records = {}  # key -> latest partial record with per-logical data
    if os.path.exists(args.output):
        latest_records = {}
        with open(args.output) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                r = json.loads(line)
                key = (str(r["A_terms"]), str(r["B_terms"]),
                       str(r["C_terms"]), str(r["D_terms"]), r["ell"], r["m"])
                latest_records[key] = r
        done_keys = set(latest_records)
        partial_records = {
            key: record for key, record in latest_records.items()
            if not record.get("milp_exact_deep", False)
        }
        if args.rerun_partial:
            print(f"  Resuming: {len(done_keys)} already verified, "
                  f"{len(partial_records)} partial (will re-run unsolved logicals)")
            done_keys -= set(partial_records.keys())
        else:
            print(f"  Resuming: {len(done_keys)} already verified")

    selected_keys = {
        (str(c["A_terms"]), str(c["B_terms"]), str(c["C_terms"]),
         str(c["D_terms"]), c["ell"], c["m"])
        for c in trusted
    }
    blocked_partials = selected_keys & set(partial_records)
    if hash_filter is not None and blocked_partials and not args.rerun_partial:
        parser.error(
            "explicit worklist contains existing partial results; pass "
            "--rerun-partial so they are not silently treated as complete"
        )

    todo = []
    for c in trusted:
        key = (str(c["A_terms"]), str(c["B_terms"]),
               str(c["C_terms"]), str(c["D_terms"]), c["ell"], c["m"])
        if key not in done_keys:
            todo.append(c)

    if args.plan_only:
        print(f"  Plan only: {len(todo)} codes remain")
        for code in todo:
            print(f"    {code.get('bliss_hash', '<no-hash>')} "
                  f"[[{code.get('n')},{code.get('k')},<={code.get('d')}]] "
                  f"trust={code.get('trust_level')}")
        return

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
