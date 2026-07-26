"""Publication-quality verification of all Campaign 7 non-CSS PBB codes.

Deduplication via BLISS canonical Tanner graph hashing, extended MILP budgets,
more BP-OSD trials, incremental output with resume support.

Designed to run alongside the evolution campaign using idle cores/RAM.

Output: results/campaign7_publication.jsonl -- one JSON record per code,
written immediately on completion so no results are lost on interruption.

Usage:
    # Default: 8 workers, all lattices, resume from existing output
    uv run python scripts/verify_publication.py

    # Custom workers (leave headroom for campaign)
    uv run python scripts/verify_publication.py --workers 6

    # Skip already-exact codes (they don't need re-verification)
    uv run python scripts/verify_publication.py --skip-exact
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
import warnings
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path

warnings.filterwarnings("ignore", message=".*datetime.datetime.utcnow.*", category=DeprecationWarning)

PROJECT_ROOT = str(Path(__file__).resolve().parent.parent)
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

CODES_JSONL = "results/evolution/campaign7/all_codes_noncss.jsonl"
OUTPUT_FILE = "results/campaign7_publication.jsonl"


# ---------------------------------------------------------------------------
# BLISS canonical hashing for non-CSS PBB codes
# ---------------------------------------------------------------------------

def bliss_canonical_hash(ell: int, m: int, A_terms, B_terms, C_terms, D_terms) -> str:
    """Compute BLISS canonical hash of a non-CSS PBB code's Tanner graph.

    Two codes with the same hash are isomorphic (identical up to qubit/check
    relabeling). This is the definitive equivalence check -- more reliable
    than polynomial-level comparisons which miss non-diagonal automorphisms.

    The Tanner graph has 3 node colors:
      - color 0: n qubit nodes
      - color 1: n_checks nodes for X-support edges
      - color 2: n_checks nodes for Z-support edges

    This captures the full symplectic structure of non-CSS stabilizers.
    Returns a 16-char hex hash (SHA-256 truncated).
    """
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
        # stabilizer.  Without this edge BLISS would permit independent row
        # permutations of the X- and Z-parts (sigma_X != sigma_Z), deciding a
        # relation strictly broader than stabilizer permutation equivalence.
        # See evaluation/tanner_equivalence.py "Non-CSS extension" for the
        # full argument.
        edges.append((n + j, n + n_checks + j))
    g.add_edges(edges)

    canon_perm = g.canonical_permutation(color=colors)
    g_canon = g.permute_vertices(canon_perm)
    canon_edges = tuple(sorted(g_canon.get_edgelist()))
    return hashlib.sha256(str(canon_edges).encode()).hexdigest()[:16]


# ---------------------------------------------------------------------------
# Publication-quality verification worker
# ---------------------------------------------------------------------------

def publication_verify_worker(task: tuple) -> dict:
    """Verify a single code with publication-quality MILP budgets.

    MILP budgets (much longer than evolution or first verification):
      n <= 108:  300s/logical,  1800s total  (vs 15s/90s in evolution)
      n <= 216:  600s/logical,  3600s total  (vs 30s/180s in evolution)
      n >  216:  900s/logical,  5400s total  (vs 60s/360s in evolution)

    BP-OSD: 1000 trials x 3 seeds + 500 trials x 2 seeds.
    """
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
                "d_is_exact": False, "time_s": 0.0, "publication_quality": True}

    # --- Stage 1: Hash-based exact check ---
    from evaluation.distance_bposd_noncss import has_low_weight_logical

    max_weight = 6 if n <= 216 else 4
    found, d_exact = has_low_weight_logical(code, max_weight=max_weight)
    if found:
        import math
        elapsed = time.time() - t0
        fom = 0.0 if d_exact <= 4 else (k * d_exact * d_exact / n)
        return {
            **base,
            "d": d_exact, "d_method": f"exact_w{d_exact}",
            "d_is_exact": True,
            "fom": round(fom, 4),
            "d_over_sqrtn": round(d_exact / math.sqrt(n), 3) if n > 0 else 0,
            "trust_level": "EXACT",
            "time_s": round(elapsed, 1),
            "publication_quality": True,
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
        import math
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
            "d_over_sqrtn": round(d_best / math.sqrt(n), 3) if n > 0 else 0,
            "trust_level": "EXACT",
            "time_s": round(elapsed, 1),
            "publication_quality": True,
        }

    # --- Stage 3: BP-OSD with extensive trials ---
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

    # publication_quality = True only when distance is provably exact.
    # For upper bounds, trust_level indicates confidence:
    #   EXACT:     d is proven (hash check or MILP solved all logicals)
    #   TRUSTED:   d/sqrt(n) < 1.5 -- consistent with random coding bound
    #   PARTIAL:   d/sqrt(n) < 2.5 -- plausible but less certain
    #   UNTRUSTED: d/sqrt(n) >= 2.5 -- likely overestimate
    import math
    bposd_spread = max(d_bp_runs) - min(d_bp_runs)
    ratio = d_best / math.sqrt(n) if n > 0 else 0
    if milp_exact:
        trust_level = "EXACT"
    elif ratio < 1.5:
        trust_level = "TRUSTED"
    elif ratio < 2.5:
        trust_level = "PARTIAL"
    else:
        trust_level = "UNTRUSTED"

    return {
        **base,
        "d": d_best, "d_method": method,
        "d_is_exact": milp_exact,
        "d_is_upper_bound": not milp_exact,
        "d_milp": d_milp if milp_worked else None,
        "d_bposd": d_bp,
        "d_bposd_runs": d_bp_runs,
        "bposd_spread": bposd_spread,
        "milp_solved": milp_solved,
        "milp_total_logicals": milp_total_logicals,
        "milp_budget": f"{milp_tpl}s/logical, {milp_total}s total",
        "fom": round(fom, 4),
        "d_over_sqrtn": round(ratio, 3),
        "trust_level": trust_level,
        "time_s": round(elapsed, 1),
        "publication_quality": milp_exact,
    }


# ---------------------------------------------------------------------------
# Loading and deduplication
# ---------------------------------------------------------------------------

def _tuple_key(c: dict) -> str:
    """Polynomial-tuple key for initial deduplication."""
    def canonical_terms(name: str) -> list:
        return sorted([list(t) for t in c.get(name, [])])

    return json.dumps(
        [canonical_terms("A_terms"), canonical_terms("B_terms"),
         canonical_terms("C_terms"), canonical_terms("D_terms"),
         c.get("ell"), c.get("m")],
        sort_keys=True,
    )


def load_and_deduplicate(jsonl_path: str, min_d: int = 5) -> list[dict]:
    """Load codes, tuple-deduplicate, filter to d >= min_d and k > 0."""
    codes = []
    with open(jsonl_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            codes.append(json.loads(line))

    seen = set()
    unique = []
    for c in codes:
        if c.get("k", 0) <= 0 or c.get("d", 0) < min_d:
            continue
        key = _tuple_key(c)
        if key not in seen:
            seen.add(key)
            unique.append(c)

    return unique


def bliss_deduplicate(codes: list[dict]) -> list[dict]:
    """Deduplicate codes using BLISS canonical Tanner graph hashing.

    This catches isomorphic codes that have different polynomial
    representations (e.g., related by lattice automorphisms).
    Keeps the code with the highest original FOM for each hash.
    """
    print("  Computing BLISS canonical hashes...")
    hash_map: dict[str, dict] = {}  # bliss_hash -> best code
    t0 = time.time()

    for i, c in enumerate(codes):
        try:
            A = [tuple(t) for t in c["A_terms"]]
            B = [tuple(t) for t in c["B_terms"]]
            C = [tuple(t) for t in c["C_terms"]]
            D = [tuple(t) for t in c["D_terms"]]
            h = bliss_canonical_hash(c["ell"], c["m"], A, B, C, D)
            c["_bliss_hash"] = h

            if h not in hash_map or c.get("fom", 0) > hash_map[h].get("fom", 0):
                hash_map[h] = c
        except Exception:
            # Keep codes that fail BLISS (shouldn't happen, but be safe)
            fallback_key = f"fallback_{_tuple_key(c)}"
            c["_bliss_hash"] = fallback_key
            hash_map[fallback_key] = c

        if (i + 1) % 50 == 0 or i + 1 == len(codes):
            elapsed = time.time() - t0
            print(f"    {i+1}/{len(codes)} hashed ({elapsed:.1f}s), "
                  f"{len(hash_map)} unique so far")

    deduped = list(hash_map.values())
    n_removed = len(codes) - len(deduped)
    print(f"  BLISS dedup: {len(codes)} -> {len(deduped)} "
          f"({n_removed} isomorphic duplicates removed)")
    return deduped


def load_already_verified(output_path: str) -> set[str]:
    """Load BLISS hashes of already-verified codes for resume support."""
    done = set()
    if not Path(output_path).exists():
        return done
    with open(output_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                c = json.loads(line)
                bh = c.get("bliss_hash")
                if bh:
                    done.add(bh)
            except json.JSONDecodeError:
                continue
    return done


def prioritize(codes: list[dict], skip_exact: bool = False) -> list[dict]:
    """Sort codes for optimal verification order.

    Priority:
    1. Small exact codes first (fast, fills output quickly)
    2. Then by lattice size ascending (faster codes first)
    3. Within each group, by FOM descending (most important first)
    """
    exact = []
    needs_verify = []

    for c in codes:
        method = c.get("d_method", "")
        if method.startswith("exact") or method == "milp_exact":
            if not skip_exact:
                exact.append(c)
        else:
            needs_verify.append(c)

    exact.sort(key=lambda x: x.get("fom", 0), reverse=True)
    needs_verify.sort(key=lambda x: (x.get("n", 0), -x.get("fom", 0)))

    return exact + needs_verify


def main():
    parser = argparse.ArgumentParser(
        description="Publication-quality verification of Campaign 7 codes"
    )
    parser.add_argument("--workers", type=int, default=8,
                        help="Parallel workers (default: 8)")
    parser.add_argument("--input", type=str, default=CODES_JSONL)
    parser.add_argument("--output", type=str, default=OUTPUT_FILE)
    parser.add_argument("--skip-exact", action="store_true",
                        help="Skip already-exact codes")
    parser.add_argument("--max-codes", type=int, default=None,
                        help="Max codes to verify (for testing)")
    parser.add_argument("--no-bliss", action="store_true",
                        help="Skip BLISS dedup (use tuple dedup only)")
    parser.add_argument("--rerun-bad", action="store_true",
                        help="Re-run codes with bad MILP metadata or pub_quality=false")
    args = parser.parse_args()

    print(f"Publication-quality verification -- Campaign 7")
    print(f"{'=' * 70}")
    print(f"Input:   {args.input}")
    print(f"Output:  {args.output}")
    print(f"Workers: {args.workers}")
    print(f"BLISS:   {'disabled' if args.no_bliss else 'enabled'}")
    print(f"Start:   {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()

    # Load, tuple-deduplicate, filter
    print("Loading codes...")
    codes = load_and_deduplicate(args.input)
    print(f"  {len(codes)} unique codes (tuple-dedup) with d>=5, k>0")

    # BLISS deduplication
    if not args.no_bliss:
        codes = bliss_deduplicate(codes)
    else:
        for c in codes:
            c["_bliss_hash"] = _tuple_key(c)

    # Save deduplicated codes (before verification) so we have a clean list
    dedup_path = Path(args.output).with_suffix(".dedup.jsonl")
    print(f"  Saving deduplicated codes to {dedup_path}...")
    with open(dedup_path, "w") as f_dedup:
        for c in sorted(codes, key=lambda x: x.get("fom", 0), reverse=True):
            record = {
                "bliss_hash": c.get("_bliss_hash", ""),
                "ell": c["ell"], "m": c["m"],
                "n": c.get("n", 2 * c["ell"] * c["m"]),
                "k": c.get("k", 0), "d": c.get("d", 0),
                "fom": c.get("fom", 0.0),
                "d_method": c.get("d_method", ""),
                "A_terms": c["A_terms"], "B_terms": c["B_terms"],
                "C_terms": c["C_terms"], "D_terms": c["D_terms"],
            }
            f_dedup.write(json.dumps(record) + "\n")
    print(f"  Saved {len(codes)} deduplicated codes")

    # Check for resume / rerun-bad
    already_done = load_already_verified(args.output)

    if args.rerun_bad and Path(args.output).exists():
        import math
        # Identify bad entries and backfill new fields on good entries
        good_results = []
        bad_hashes = set()
        with open(args.output) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                r = json.loads(line)
                method = r.get("d_method", "")
                has_bad_meta = (
                    method in ("milp+bposd", "bposd")
                    and r.get("milp_solved", 0) == 0
                    and r.get("milp_total_logicals", 0) == 0
                    and r.get("k", 0) > 0
                )
                if has_bad_meta or not r.get("publication_quality", True):
                    bad_hashes.add(r.get("bliss_hash"))
                else:
                    # Backfill new fields if missing
                    if "trust_level" not in r:
                        n_val = r.get("n", 1)
                        d_val = r.get("d", 0)
                        ratio = d_val / math.sqrt(n_val) if n_val > 0 else 0
                        r["d_over_sqrtn"] = round(ratio, 3)
                        if r.get("d_is_exact"):
                            r["trust_level"] = "EXACT"
                        elif ratio < 1.5:
                            r["trust_level"] = "TRUSTED"
                        elif ratio < 2.5:
                            r["trust_level"] = "PARTIAL"
                        else:
                            r["trust_level"] = "UNTRUSTED"
                    if "bposd_spread" not in r:
                        runs = r.get("d_bposd_runs", [])
                        r["bposd_spread"] = (
                            max(runs) - min(runs) if runs else 0
                        )
                    good_results.append(r)
        # Rewrite output with backfilled good results
        with open(args.output, "w") as f:
            for r in good_results:
                f.write(json.dumps(r) + "\n")
        already_done -= bad_hashes
        print(f"  Rerun-bad: removed {len(bad_hashes)} entries, "
              f"backfilled {len(good_results)} good results")

    if already_done:
        codes = [c for c in codes if c.get("_bliss_hash") not in already_done]
        print(f"  Resuming: {len(already_done)} already verified, "
              f"{len(codes)} remaining")

    # Prioritize
    codes = prioritize(codes, skip_exact=args.skip_exact)
    if args.max_codes:
        codes = codes[:args.max_codes]

    # Summary by lattice
    from collections import Counter
    lat_counts = Counter((c["ell"], c["m"]) for c in codes)
    print(f"\nCodes to verify: {len(codes)}")
    for lat in sorted(lat_counts.keys()):
        print(f"  ({lat[0]},{lat[1]}) n={2*lat[0]*lat[1]}: {lat_counts[lat]}")

    if not codes:
        print("\nNothing to verify!")
        return

    # Build tasks
    tasks = []
    for i, c in enumerate(codes):
        code_id = f"{c['ell']}_{c['m']}_{i:04d}"
        tasks.append((
            c["ell"], c["m"],
            [tuple(t) for t in c["A_terms"]],
            [tuple(t) for t in c["B_terms"]],
            [tuple(t) for t in c["C_terms"]],
            [tuple(t) for t in c["D_terms"]],
            c.get("_bliss_hash", ""),
            code_id,
        ))

    # Run verification
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    completed = 0
    errors = 0
    best_per_lattice: dict[tuple, dict] = {}
    t_start = time.time()

    print(f"\n{'#':>4} {'lattice':>8} {'n':>4} {'k':>3} {'d':>4} "
          f"{'FOM':>8} {'method':>15} {'time':>7} {'quality':>8}")
    print("-" * 75)

    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(publication_verify_worker, task): i
                   for i, task in enumerate(tasks)}

        with open(output_path, "a") as f_out:
            for future in as_completed(futures, timeout=36000):
                idx = futures[future]
                try:
                    result = future.result()
                    completed += 1

                    f_out.write(json.dumps(result) + "\n")
                    f_out.flush()

                    lat = (result["ell"], result["m"])
                    if (lat not in best_per_lattice
                            or result["fom"] > best_per_lattice[lat]["fom"]):
                        best_per_lattice[lat] = result

                    qual = "EXACT" if result.get("d_is_exact") else "bound"
                    elapsed_total = time.time() - t_start
                    rate = completed / elapsed_total if elapsed_total > 0 else 0
                    remaining = len(tasks) - completed
                    eta_s = remaining / rate if rate > 0 else 0

                    print(
                        f"{completed:4d} ({result['ell']},{result['m']})"
                        f" {result['n']:5d} {result['k']:3d} {result['d']:4d}"
                        f" {result['fom']:8.2f} {result['d_method']:>15}"
                        f" {result['time_s']:6.1f}s {qual:>8}"
                        f"  [{completed}/{len(tasks)},"
                        f" ETA {eta_s / 3600:.1f}h]"
                    )
                except Exception as e:
                    errors += 1
                    print(f"  ERROR on task {idx}: {e}")

    elapsed_total = time.time() - t_start

    # ── Final summary ─────────────────────────────────────────────
    print(f"\n{'=' * 75}")
    print(f"VERIFICATION COMPLETE")
    print(f"{'=' * 75}")
    print(f"Completed: {completed}/{len(tasks)} ({errors} errors)")
    print(f"Wall time: {elapsed_total / 3600:.1f} hours")
    print(f"Output:    {output_path}")

    # Load full output for summary (includes resumed results)
    all_results = []
    with open(output_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                all_results.append(json.loads(line))
            except json.JSONDecodeError:
                continue

    # Deduplicate output by bliss_hash (in case of double-runs)
    seen_hashes = set()
    deduped_results = []
    for r in all_results:
        bh = r.get("bliss_hash", "")
        if bh and bh in seen_hashes:
            continue
        seen_hashes.add(bh)
        deduped_results.append(r)

    exact_count = sum(1 for r in deduped_results if r.get("d_is_exact"))
    bound_count = sum(1 for r in deduped_results if r.get("d_is_upper_bound"))
    from collections import Counter
    trust_counts = Counter(r.get("trust_level", "?") for r in deduped_results)
    print(f"\nTotal unique verified codes: {len(deduped_results)}")
    print(f"  Exact distances:   {exact_count}")
    print(f"  Upper bounds:      {bound_count}")
    print(f"  Trust levels:      {dict(trust_counts.most_common())}")

    # Best per lattice
    best_per_lattice = {}
    for r in deduped_results:
        lat = (r["ell"], r["m"])
        if lat not in best_per_lattice or r["fom"] > best_per_lattice[lat]["fom"]:
            best_per_lattice[lat] = r

    print(f"\nBEST VERIFIED CODE PER LATTICE:")
    print(f"{'Lattice':>8} {'Code':>16} {'FOM':>8} {'Method':>15}"
          f" {'Trust':>10} {'d/√n':>6}")
    print("-" * 70)
    for lat in sorted(best_per_lattice.keys()):
        r = best_per_lattice[lat]
        trust = r.get("trust_level", "?")
        ratio = r.get("d_over_sqrtn", 0)
        code_str = f"[[{r['n']},{r['k']},{r['d']}]]"
        print(f"({lat[0]:2d},{lat[1]:2d}) {code_str:>16} {r['fom']:8.2f}"
              f" {r['d_method']:>15} {trust:>10} {ratio:6.3f}")

    # Publication table: FOM > 6.0
    print(f"\nCODES WITH FOM > 6.0:")
    above = sorted(
        [r for r in deduped_results if r["fom"] > 6.0],
        key=lambda x: x["fom"], reverse=True,
    )
    if above:
        print(f"{'Code':>16} {'FOM':>8} {'Lattice':>8} {'Method':>15}"
              f" {'Trust':>10} {'d/√n':>6} {'MILP':>12}")
        print("-" * 90)
        for r in above[:30]:
            trust = r.get("trust_level", "?")
            ratio = r.get("d_over_sqrtn", 0)
            milp_s = f"{r.get('milp_solved', '?')}/{r.get('milp_total_logicals', '?')}"
            code_str = f"[[{r['n']},{r['k']},{r['d']}]]"
            print(f"{code_str:>16} {r['fom']:8.2f} ({r['ell']:2d},{r['m']:2d})"
                  f" {r['d_method']:>15} {trust:>10} {ratio:6.3f} {milp_s:>12}")
    else:
        print("  None yet.")


if __name__ == "__main__":
    main()
