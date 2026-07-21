"""Verify top non-CSS PBB codes from Campaign 7 with extended MILP budgets.

Reads all_codes_noncss.jsonl, deduplicates, selects top codes per lattice,
and re-verifies with much longer MILP timeouts than the evolution pipeline.

Usage:
    # Default: top 5 per lattice, 4 workers
    uv run python scripts/verify_campaign7.py

    # More codes, more workers
    uv run python scripts/verify_campaign7.py --top 10 --workers 8

    # Only specific lattices
    uv run python scripts/verify_campaign7.py --lattices 9,6 12,6 15,6
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

PROJECT_ROOT = str(Path(__file__).resolve().parent.parent)
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

CODES_JSONL = "results/evolution/campaign7/all_codes_noncss.jsonl"
OUTPUT_FILE = "results/campaign7_verified.jsonl"


def verify_worker(task: tuple) -> dict:
    """Re-verify a single code with extended MILP budget.

    Uses the same 3-tier pipeline as the evolution worker but with
    much longer MILP timeouts:
      - n<=216: 120s/logical, 600s total (vs 30s/180s in evolution)
      - n>216:  300s/logical, 1800s total (vs 60s/360s in evolution)

    Also runs BP-OSD with more trials for a tighter fallback bound.
    """
    ell, m, A_terms, B_terms, C_terms, D_terms, orig_fom, orig_d = task

    from evaluation.pbb_code import build_pbb_code, get_pbb_params_fast

    t0 = time.time()
    code = build_pbb_code(ell, m, A_terms, B_terms, C_terms, D_terms)
    n, k = get_pbb_params_fast(code)

    base = {
        "ell": ell, "m": m, "n": n, "k": k,
        "A_terms": A_terms, "B_terms": B_terms,
        "C_terms": C_terms, "D_terms": D_terms,
        "orig_d": orig_d, "orig_fom": orig_fom,
    }

    if k == 0:
        return {**base, "d": 0, "fom": 0.0, "d_method": "k=0", "time_s": 0.0}

    # --- Stage 1: Hash-based exact check ---
    from evaluation.distance_bposd_noncss import has_low_weight_logical

    if n <= 216:
        max_weight = 6
    else:
        max_weight = 4

    found, d_exact = has_low_weight_logical(code, max_weight=max_weight)
    if found:
        elapsed = time.time() - t0
        fom = 0.0 if d_exact <= 4 else (k * d_exact * d_exact / n)
        return {
            **base,
            "d": d_exact, "d_method": f"exact_w{d_exact}",
            "fom": round(fom, 2), "time_s": round(elapsed, 1),
        }

    # --- Stage 2: MILP with extended budget ---
    from evaluation.distance_milp import compute_distance_milp_symplectic

    if n <= 216:
        milp_tpl, milp_total = 120, 600
    else:
        milp_tpl, milp_total = 300, 1800

    try:
        d_milp, details = compute_distance_milp_symplectic(
            code,
            timeout_per_logical=milp_tpl,
            total_timeout=milp_total,
            early_stop=None,
            verbose=False,
        )
        milp_exact = details.get("exact", False)
        milp_worked = d_milp < n
        milp_solved = details.get("num_solved", 0)
        milp_total_logicals = details.get("num_logicals", 0)
    except Exception:
        d_milp = n
        milp_exact = False
        milp_worked = False
        milp_solved = 0
        milp_total_logicals = 0

    if milp_exact:
        d_best = d_milp
        elapsed = time.time() - t0
        fom = k * d_best * d_best / n if n > 0 else 0.0
        return {
            **base,
            "d": d_best, "d_method": "milp_exact",
            "d_milp": d_milp, "milp_solved": milp_solved,
            "milp_total_logicals": milp_total_logicals,
            "fom": round(fom, 2), "time_s": round(elapsed, 1),
        }

    # --- Stage 3: BP-OSD with more trials ---
    from evaluation.distance_bposd_noncss import estimate_distance_noncss

    d_bp1 = estimate_distance_noncss(code, num_trials=500, seed=42)
    d_bp2 = estimate_distance_noncss(code, num_trials=500, seed=137)
    d_bp3 = estimate_distance_noncss(code, num_trials=300, seed=271)
    d_bp = min(d_bp1, d_bp2, d_bp3)

    d_best = min(d_milp, d_bp) if milp_worked else d_bp
    elapsed = time.time() - t0
    fom = k * d_best * d_best / n if d_best > 0 and n > 0 else 0.0

    method = "milp+bposd" if milp_worked else "bposd"

    return {
        **base,
        "d": d_best, "d_method": method,
        "d_milp": d_milp if milp_worked else None,
        "d_bposd": d_bp,
        "milp_solved": milp_solved,
        "milp_total_logicals": milp_total_logicals,
        "fom": round(fom, 2), "time_s": round(elapsed, 1),
    }


def load_codes(jsonl_path: str) -> list[dict]:
    codes = []
    with open(jsonl_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            codes.append(json.loads(line))
    return codes


def select_top_codes(
    codes: list[dict],
    top_per_lattice: int,
    lattice_filter: list[tuple[int, int]] | None = None,
) -> list[dict]:
    """Deduplicate and select top codes per lattice for verification."""
    # Only select codes that used milp+bposd or bposd (not already exact)
    seen = set()
    by_lattice: dict[tuple, list[dict]] = {}

    for c in sorted(codes, key=lambda x: x.get("fom", 0), reverse=True):
        if c.get("d_method", "").startswith("exact"):
            continue
        key = (
            str(c.get("A_terms")),
            str(c.get("B_terms")),
            str(c.get("C_terms")),
            str(c.get("D_terms")),
            c.get("ell"),
            c.get("m"),
        )
        if key in seen:
            continue
        seen.add(key)

        lattice = (c.get("ell"), c.get("m"))
        if lattice_filter and lattice not in lattice_filter:
            continue
        by_lattice.setdefault(lattice, []).append(c)

    selected = []
    for lattice in sorted(by_lattice.keys()):
        top = by_lattice[lattice][:top_per_lattice]
        selected.extend(top)
        print(f"  ({lattice[0]},{lattice[1]}): {len(top)} codes to verify "
              f"(top FOM={top[0]['fom']:.2f})")

    return selected


def main():
    parser = argparse.ArgumentParser(description="Verify top Campaign 7 codes")
    parser.add_argument("--top", type=int, default=5,
                        help="Top N codes per lattice to verify (default: 5)")
    parser.add_argument("--workers", type=int, default=4,
                        help="Number of parallel workers (default: 4)")
    parser.add_argument("--lattices", type=str, nargs="+", default=None,
                        help="Lattices to verify (e.g. 9,6 12,6). Default: all.")
    parser.add_argument("--input", type=str, default=CODES_JSONL,
                        help="Input JSONL file")
    parser.add_argument("--output", type=str, default=OUTPUT_FILE,
                        help="Output JSONL file")
    args = parser.parse_args()

    lattice_filter = None
    if args.lattices:
        lattice_filter = []
        for s in args.lattices:
            parts = s.split(",")
            lattice_filter.append((int(parts[0]), int(parts[1])))

    print(f"Loading codes from {args.input}...")
    codes = load_codes(args.input)
    print(f"  {len(codes)} total codes")

    print(f"\nSelecting top {args.top} per lattice:")
    selected = select_top_codes(codes, args.top, lattice_filter)
    print(f"\n{len(selected)} codes to verify with {args.workers} workers")

    # Build tasks
    tasks = []
    for c in selected:
        tasks.append((
            c["ell"], c["m"],
            [tuple(t) for t in c["A_terms"]],
            [tuple(t) for t in c["B_terms"]],
            [tuple(t) for t in c["C_terms"]],
            [tuple(t) for t in c["D_terms"]],
            c.get("fom", 0),
            c.get("d", 0),
        ))

    # Run verification
    results = []
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    t_start = time.time()
    print(f"\nStarting verification...")
    print(f"{'#':>3} {'lattice':>8} {'n':>4} {'k':>3} {'orig_d':>6} {'new_d':>5} "
          f"{'orig_FOM':>9} {'new_FOM':>8} {'method':>15} {'time':>7}")
    print("-" * 85)

    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(verify_worker, task): i for i, task in enumerate(tasks)}

        with open(output_path, "w") as f_out:
            for future in as_completed(futures, timeout=7200):
                idx = futures[future]
                try:
                    result = future.result()
                    results.append(result)

                    # Write to JSONL immediately
                    f_out.write(json.dumps(result) + "\n")
                    f_out.flush()

                    # Print result
                    changed = "***" if result["d"] != result["orig_d"] else "   "
                    print(
                        f"{len(results):3d} ({result['ell']},{result['m']})"
                        f" {result['n']:5d} {result['k']:3d}"
                        f" {result['orig_d']:6d} {result['d']:5d}"
                        f" {result['orig_fom']:9.2f} {result['fom']:8.2f}"
                        f" {result['d_method']:>15} {result['time_s']:6.1f}s"
                        f" {changed}"
                    )
                except Exception as e:
                    print(f"  ERROR on task {idx}: {e}")

    elapsed = time.time() - t_start
    print(f"\nVerification complete in {elapsed:.0f}s")
    print(f"Results written to {output_path}")

    # Summary
    print(f"\n{'='*85}")
    print("SUMMARY -- Best verified FOM per lattice:")
    print(f"{'='*85}")
    by_lattice: dict[tuple, dict] = {}
    for r in results:
        lat = (r["ell"], r["m"])
        if lat not in by_lattice or r["fom"] > by_lattice[lat]["fom"]:
            by_lattice[lat] = r

    for lat in sorted(by_lattice.keys()):
        r = by_lattice[lat]
        orig = f"(was d={r['orig_d']}, FOM={r['orig_fom']:.2f})"
        print(f"  ({lat[0]},{lat[1]}) n={r['n']}: "
              f"[[{r['n']},{r['k']},{r['d']}]] FOM={r['fom']:.2f} "
              f"method={r['d_method']} {orig}")

    # Highlight improvements over FOM=6.0
    print(f"\nCodes with verified FOM > 6.0:")
    above = [r for r in results if r["fom"] > 6.0 and r["d_method"] != "bposd"]
    if above:
        for r in sorted(above, key=lambda x: x["fom"], reverse=True):
            print(f"  [[{r['n']},{r['k']},{r['d']}]] FOM={r['fom']:.2f} "
                  f"({r['ell']},{r['m']}) method={r['d_method']}")
    else:
        print("  None yet.")


if __name__ == "__main__":
    main()
