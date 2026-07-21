"""Full from-scratch verification: BLISS dedup + publication-quality verification.

Starts from raw evolution JSONL, does a SINGLE-PASS BLISS dedup of all
tuple-unique codes, cross-references with existing verified results,
and verifies any missing codes.

Usage:
    # Step 1: Dedup only (fast, ~5min)
    uv run python scripts/verify_from_scratch.py --dedup-only

    # Step 2: Verify missing codes
    uv run python scripts/verify_from_scratch.py --workers 4

    # Full pipeline
    uv run python scripts/verify_from_scratch.py --workers 8
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import sys
import time
import warnings
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path

warnings.filterwarnings("ignore", message=".*datetime.datetime.utcnow.*",
                        category=DeprecationWarning)

PROJECT_ROOT = str(Path(__file__).resolve().parent.parent)
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

RAW_CODES = "results/evolution/campaign7/all_codes_noncss.jsonl"
DEDUP_FILE = "results/campaign7_dedup.jsonl"
VERIFIED_FILE = "results/campaign7_verified_all.jsonl"


# ---------------------------------------------------------------------------
# BLISS canonical hashing
# ---------------------------------------------------------------------------

def bliss_canonical_hash(ell, m, A_terms, B_terms, C_terms, D_terms):
    """Compute BLISS canonical hash of a non-CSS PBB code's Tanner graph."""
    import igraph as ig
    import numpy as np
    from evaluation.pbb_code import build_pbb_code

    code = build_pbb_code(ell, m, A_terms, B_terms, C_terms, D_terms)
    H = np.array(code.matrix.toarray() if hasattr(code.matrix, "toarray")
                 else code.matrix) % 2
    n_checks, two_n = H.shape
    n = two_n // 2
    H_X, H_Z = H[:, :n], H[:, n:]

    total_nodes = n + 2 * n_checks
    g = ig.Graph(total_nodes, directed=False)
    colors = [0] * n + [1] * n_checks + [2] * n_checks
    edges = []
    for j in range(n_checks):
        for i in range(n):
            if H_X[j, i]:
                edges.append((i, n + j))
            if H_Z[j, i]:
                edges.append((i, n + n_checks + j))
        # Tie X-support vertex j to Z-support vertex j so any color-respecting
        # graph isomorphism preserves the (X-part, Z-part) pairing of each
        # stabilizer.  See evaluation/tanner_equivalence.py "Non-CSS extension"
        # for the full argument.
        edges.append((n + j, n + n_checks + j))
    g.add_edges(edges)

    canon_perm = g.canonical_permutation(color=colors)
    g_canon = g.permute_vertices(canon_perm)
    canon_edges = tuple(sorted(g_canon.get_edgelist()))
    return hashlib.sha256(str(canon_edges).encode()).hexdigest()[:16]


def hash_worker(task):
    """Worker to compute BLISS hash for a single code."""
    idx, code_data = task
    try:
        A = [tuple(t) for t in code_data["A_terms"]]
        B = [tuple(t) for t in code_data["B_terms"]]
        C = [tuple(t) for t in code_data.get("C_terms", [])]
        D = [tuple(t) for t in code_data.get("D_terms", [])]
        h = bliss_canonical_hash(code_data["ell"], code_data["m"], A, B, C, D)
        return idx, h, None
    except Exception as e:
        return idx, None, str(e)


# ---------------------------------------------------------------------------
# Publication-quality verification worker (from verify_publication.py)
# ---------------------------------------------------------------------------

def publication_verify_worker(task):
    """Verify a single code with publication-quality MILP budgets."""
    ell, m, A_terms, B_terms, C_terms, D_terms, bliss_hash, code_id = task
    from evaluation.pbb_code import build_pbb_code, get_pbb_params_fast

    t0 = time.time()
    code = build_pbb_code(ell, m, A_terms, B_terms, C_terms, D_terms)
    n, k = get_pbb_params_fast(code)

    base = {
        "code_id": code_id,
        "bliss_hash": bliss_hash,
        "ell": ell, "m": m, "n": n, "k": k,
        "A_terms": A_terms, "B_terms": B_terms,
        "C_terms": C_terms, "D_terms": D_terms,
        "verified_at": datetime.now(timezone.utc).isoformat(),
    }

    if k == 0:
        return {**base, "d": 0, "fom": 0.0, "d_method": "k=0",
                "d_is_exact": False, "time_s": 0.0,
                "trust_level": "EXACT"}

    # --- Stage 1: Hash-based exact check ---
    from evaluation.distance_bposd_noncss import has_low_weight_logical

    max_weight = 6 if n <= 216 else 4
    found, d_exact = has_low_weight_logical(code, max_weight=max_weight)
    if found:
        elapsed = time.time() - t0
        fom = 0.0 if d_exact <= 4 else (k * d_exact * d_exact / n)
        return {
            **base,
            "d": d_exact, "d_method": f"exact_w{d_exact}",
            "d_is_exact": True,
            "fom": round(fom, 4),
            "d_over_sqrtn": round(d_exact / math.sqrt(n), 3),
            "trust_level": "EXACT",
            "time_s": round(elapsed, 1),
        }

    # --- Stage 2: MILP with publication-quality budgets ---
    from evaluation.distance_milp import compute_distance_milp_symplectic

    if n <= 108:
        milp_tpl, milp_total = 300, 1800
    elif n <= 216:
        milp_tpl, milp_total = 600, 3600
    else:
        milp_tpl, milp_total = 900, 5400

    d_milp = n
    milp_exact = False
    milp_worked = False
    milp_details = {}
    try:
        d_milp, milp_details = compute_distance_milp_symplectic(
            code,
            timeout_per_logical=milp_tpl,
            total_timeout=milp_total,
            early_stop=None,
            verbose=False,
        )
        milp_exact = milp_details.get("exact", False)
        milp_worked = d_milp < n
    except Exception as e:
        milp_details = {"error": str(e)}

    milp_solved = milp_details.get("num_logicals_checked", 0)
    milp_total_logicals = milp_details.get("total_logicals", 0)

    if milp_exact:
        d_best = d_milp
        elapsed = time.time() - t0
        fom = k * d_best * d_best / n if n > 0 else 0.0
        return {
            **base,
            "d": d_best, "d_method": "milp_exact",
            "d_is_exact": True,
            "d_milp": d_milp,
            "milp_solved": milp_solved,
            "milp_total_logicals": milp_total_logicals,
            "milp_budget": f"{milp_tpl}s/logical, {milp_total}s total",
            "fom": round(fom, 4),
            "d_over_sqrtn": round(d_best / math.sqrt(n), 3),
            "trust_level": "EXACT",
            "time_s": round(elapsed, 1),
        }

    # --- Stage 3: BP-OSD ---
    from evaluation.distance_bposd_noncss import estimate_distance_noncss

    d_bp_runs = []
    for seed, trials in [(42, 1000), (137, 1000), (271, 1000),
                         (314, 500), (997, 500)]:
        d_bp_runs.append(estimate_distance_noncss(
            code, num_trials=trials, seed=seed))
    d_bp = min(d_bp_runs)

    d_best = min(d_milp, d_bp) if milp_worked else d_bp
    elapsed = time.time() - t0
    fom = k * d_best * d_best / n if d_best > 0 and n > 0 else 0.0

    method = "milp+bposd" if milp_worked else "bposd"

    ratio = d_best / math.sqrt(n) if n > 0 else 0
    if ratio < 1.5:
        trust_level = "TRUSTED"
    elif ratio < 2.5:
        trust_level = "PARTIAL"
    else:
        trust_level = "UNTRUSTED"

    return {
        **base,
        "d": d_best, "d_method": method,
        "d_is_exact": False,
        "d_is_upper_bound": True,
        "d_milp": d_milp if milp_worked else None,
        "d_bposd": d_bp,
        "d_bposd_runs": d_bp_runs,
        "milp_solved": milp_solved,
        "milp_total_logicals": milp_total_logicals,
        "milp_budget": f"{milp_tpl}s/logical, {milp_total}s total",
        "fom": round(fom, 4),
        "d_over_sqrtn": round(ratio, 3),
        "trust_level": trust_level,
        "time_s": round(elapsed, 1),
    }


# ---------------------------------------------------------------------------
# Main pipeline
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Full from-scratch verification")
    parser.add_argument("--input", default=RAW_CODES)
    parser.add_argument("--dedup-output", default=DEDUP_FILE)
    parser.add_argument("--output", default=VERIFIED_FILE)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--hash-workers", type=int, default=8,
                        help="Workers for BLISS hashing (fast, can use more)")
    parser.add_argument("--dedup-only", action="store_true",
                        help="Only do dedup, skip verification")
    parser.add_argument("--min-d", type=int, default=5,
                        help="Only process codes with evolution d >= this")
    args = parser.parse_args()

    print(f"From-scratch verification pipeline")
    print(f"  Input: {args.input}")
    print(f"  Dedup output: {args.dedup_output}")
    print(f"  Verified output: {args.output}")
    print()

    # =======================================================================
    # STEP 1: Load raw codes and tuple-level dedup
    # =======================================================================
    print("Step 1: Loading raw codes...")
    raw = []
    with open(args.input) as f:
        for line in f:
            if line.strip():
                raw.append(json.loads(line.strip()))
    print(f"  Raw entries: {len(raw)}")

    def canonical_terms(terms):
        return tuple(sorted(tuple(t) for t in (terms or [])))

    # Tuple-level dedup (keep best FOM per unique tuple)
    seen_tuples = {}
    for c in raw:
        if c.get("k", 0) <= 0:
            continue
        if c.get("d", 0) < args.min_d:
            continue
        key = (canonical_terms(c["A_terms"]), canonical_terms(c["B_terms"]),
               canonical_terms(c.get("C_terms", [])), canonical_terms(c.get("D_terms", [])),
               c["ell"], c["m"])
        if key not in seen_tuples or c.get("fom", 0) > seen_tuples[key].get("fom", 0):
            seen_tuples[key] = c

    tuple_unique = list(seen_tuples.values())
    tuple_unique.sort(key=lambda c: ((c["ell"], c["m"]), -c.get("fom", 0)))
    print(f"  Tuple-unique with k>0, d>={args.min_d}: {len(tuple_unique)}")

    # =======================================================================
    # STEP 2: BLISS canonical hash dedup (single pass, all codes)
    # =======================================================================
    print(f"\nStep 2: BLISS hashing {len(tuple_unique)} codes with {args.hash_workers} workers...")
    t0 = time.monotonic()

    tasks = [(i, c) for i, c in enumerate(tuple_unique)]
    hashes = [None] * len(tuple_unique)
    errors = 0

    with ProcessPoolExecutor(max_workers=args.hash_workers) as pool:
        futures = {pool.submit(hash_worker, t): t[0] for t in tasks}
        done = 0
        for future in as_completed(futures):
            idx, h, err = future.result()
            if err:
                errors += 1
                print(f"  ERROR hashing code {idx}: {err}")
            else:
                hashes[idx] = h
            done += 1
            if done % 100 == 0:
                elapsed = time.monotonic() - t0
                print(f"  {done}/{len(tuple_unique)} hashed ({elapsed:.0f}s)")

    elapsed = time.monotonic() - t0
    print(f"  Hashing complete: {elapsed:.0f}s, {errors} errors")

    # Dedup by hash: keep best FOM per hash
    hash_groups = defaultdict(list)
    for i, c in enumerate(tuple_unique):
        h = hashes[i]
        if h is not None:
            hash_groups[h].append(c)

    bliss_unique = []
    for h, group in hash_groups.items():
        best = max(group, key=lambda c: c.get("fom", 0))
        best["bliss_hash"] = h
        best["bliss_group_size"] = len(group)
        bliss_unique.append(best)

    bliss_unique.sort(key=lambda c: ((c["ell"], c["m"]), -c.get("fom", 0)))
    print(f"  BLISS-unique codes: {len(bliss_unique)}")

    # Per lattice
    by_lat = defaultdict(list)
    for c in bliss_unique:
        by_lat[(c["ell"], c["m"])].append(c)
    for lat in sorted(by_lat):
        cc = by_lat[lat]
        print(f"    ({lat[0]},{lat[1]}) n={cc[0]['n']}: {len(cc)} codes")

    # Write dedup file
    with open(args.dedup_output, "w") as f:
        for c in bliss_unique:
            f.write(json.dumps(c) + "\n")
    print(f"  Saved to {args.dedup_output}")

    if args.dedup_only:
        print("\n--dedup-only: stopping here.")
        return

    # =======================================================================
    # STEP 3: Cross-reference with existing verified results
    # =======================================================================
    print(f"\nStep 3: Cross-referencing with existing verified results...")

    # Load all existing verified results by BLISS hash
    verified_by_hash = {}
    verified_files = [
        "results/campaign7_publication.jsonl",
        "results/campaign7_publication_extra.jsonl",
    ]
    for vf in verified_files:
        if not os.path.exists(vf):
            continue
        with open(vf) as f:
            for line in f:
                if not line.strip():
                    continue
                r = json.loads(line.strip())
                h = r.get("bliss_hash")
                if h:
                    # Keep result with best (lowest d if EXACT, else lowest d)
                    if h not in verified_by_hash:
                        verified_by_hash[h] = r
                    else:
                        old = verified_by_hash[h]
                        # Prefer EXACT over TRUSTED
                        if r.get("trust_level") == "EXACT" and old.get("trust_level") != "EXACT":
                            verified_by_hash[h] = r
                        elif r.get("trust_level") == old.get("trust_level") and r.get("d", 999) < old.get("d", 999):
                            verified_by_hash[h] = r

    print(f"  Existing verified results: {len(verified_by_hash)} unique hashes")

    # Find which BLISS-unique codes need verification
    already_verified = []
    needs_verification = []
    for c in bliss_unique:
        h = c["bliss_hash"]
        if h in verified_by_hash:
            # Use verified result but update polynomial tuples from our canonical choice
            v = verified_by_hash[h].copy()
            v["A_terms"] = c["A_terms"]
            v["B_terms"] = c["B_terms"]
            v["C_terms"] = c.get("C_terms", [])
            v["D_terms"] = c.get("D_terms", [])
            v["bliss_hash"] = h
            already_verified.append(v)
        else:
            needs_verification.append(c)

    print(f"  Already verified: {len(already_verified)}")
    print(f"  Needs verification: {len(needs_verification)}")

    if needs_verification:
        by_lat_new = defaultdict(list)
        for c in needs_verification:
            by_lat_new[(c["ell"], c["m"])].append(c)
        for lat in sorted(by_lat_new):
            cc = by_lat_new[lat]
            print(f"    ({lat[0]},{lat[1]}): {len(cc)} codes to verify")

    # =======================================================================
    # STEP 4: Verify missing codes
    # =======================================================================
    if needs_verification:
        print(f"\nStep 4: Verifying {len(needs_verification)} codes with {args.workers} workers...")

        tasks = []
        for c in needs_verification:
            A = [tuple(t) for t in c["A_terms"]]
            B = [tuple(t) for t in c["B_terms"]]
            C = [tuple(t) for t in c.get("C_terms", [])]
            D = [tuple(t) for t in c.get("D_terms", [])]
            tasks.append((c["ell"], c["m"], A, B, C, D,
                         c["bliss_hash"], c["bliss_hash"][:8]))

        # Sort by n (smallest first for faster initial results)
        tasks.sort(key=lambda t: 2 * t[0] * t[1])

        results = []
        t0 = time.monotonic()
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            futures = {pool.submit(publication_verify_worker, t): t for t in tasks}
            for future in as_completed(futures):
                try:
                    result = future.result()
                    results.append(result)
                    elapsed = time.monotonic() - t0
                    code_str = f"[[{result['n']},{result['k']},{result['d']}]]"
                    trust = result.get("trust_level", "?")
                    fom = result.get("fom", 0)
                    print(f"  [{len(results)}/{len(tasks)}] {code_str} "
                          f"FOM={fom:.2f} {trust} ({elapsed:.0f}s)")
                except Exception as e:
                    print(f"  ERROR: {e}")

        print(f"  Verified {len(results)} codes")
    else:
        results = []
        print("\nStep 4: No codes need verification.")

    # =======================================================================
    # STEP 5: Merge and write final output
    # =======================================================================
    print(f"\nStep 5: Building final verified dataset...")

    all_verified = already_verified + results

    # Final dedup by hash (shouldn't have dupes, but safety check)
    final_by_hash = {}
    for v in all_verified:
        h = v.get("bliss_hash")
        if h not in final_by_hash:
            final_by_hash[h] = v
        else:
            old = final_by_hash[h]
            if v.get("trust_level") == "EXACT" and old.get("trust_level") != "EXACT":
                final_by_hash[h] = v
            elif v.get("d", 999) < old.get("d", 999):
                final_by_hash[h] = v

    final = list(final_by_hash.values())
    final.sort(key=lambda c: ((c["ell"], c["m"]), -c.get("fom", 0)))

    # Ensure FOM is correct
    for c in final:
        n, k, d = c["n"], c["k"], c["d"]
        if d <= 4:
            c["fom"] = 0.0
        else:
            c["fom"] = round(k * d * d / n, 4)

    with open(args.output, "w") as f:
        for c in final:
            f.write(json.dumps(c) + "\n")

    # Summary
    exact = sum(1 for c in final if c.get("trust_level") == "EXACT")
    trusted = sum(1 for c in final if c.get("trust_level") == "TRUSTED")
    other = len(final) - exact - trusted
    params = len(set((c["n"], c["k"], c["d"]) for c in final))

    print(f"\n{'='*60}")
    print(f"FINAL DATASET: {len(final)} BLISS-unique verified codes")
    print(f"  EXACT: {exact}")
    print(f"  TRUSTED: {trusted}")
    if other:
        print(f"  OTHER: {other}")
    print(f"  Unique (n,k,d) parameter sets: {params}")
    print(f"  Output: {args.output}")

    by_lat = defaultdict(list)
    for c in final:
        by_lat[(c["ell"], c["m"])].append(c)
    for lat in sorted(by_lat):
        cc = by_lat[lat]
        e = sum(1 for c in cc if c.get("trust_level") == "EXACT")
        t = len(cc) - e
        best = max(cc, key=lambda x: x.get("fom", 0))
        print(f"  ({lat[0]},{lat[1]}) n={cc[0]['n']}: {len(cc)} codes "
              f"({e}E/{t}T) best={best.get('fom',0):.2f}")


if __name__ == "__main__":
    main()
