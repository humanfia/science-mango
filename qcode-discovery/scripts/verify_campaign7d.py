#!/usr/bin/env python3
"""Verify top codes from Campaign 7d with multi-tier distance validation.

Tier 1: Extend has_low_weight_logical to weight 3-4 (seconds per code)
Tier 2: OSD-CS (order 10) with many seeds (minutes per code)
Tier 3: Symplectic MILP -- exact or near-exact distance (minutes per code)

Usage:
    uv run python scripts/verify_campaign7d.py                    # all tiers, top 20
    uv run python scripts/verify_campaign7d.py --tier 1           # quick filter only
    uv run python scripts/verify_campaign7d.py --tier 2           # up to OSD-CS
    uv run python scripts/verify_campaign7d.py --top 5            # top 5 only
    uv run python scripts/verify_campaign7d.py --milp-timeout 120 # longer MILP
"""

import argparse
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from evaluation.pbb_code import build_pbb_code, get_pbb_params_fast
from evaluation.distance_bposd_noncss import (
    estimate_distance_noncss,
    has_low_weight_logical,
)


# ---------------------------------------------------------------------------
# Tier 1: Extended low-weight check (weight 3 and 4)
# ---------------------------------------------------------------------------

def check_low_weight_symplectic(code, max_weight=4):
    """Check for nontrivial low-weight symplectic logicals.

    This wrapper preserves the script's historical API while delegating to the
    shared hash-based checker, which verifies both zero stabilizer syndrome and
    nontriviality outside the stabilizer group.
    """
    return has_low_weight_logical(code, max_weight=max_weight)


# ---------------------------------------------------------------------------
# Tier 2: Multi-seed OSD-CS
# ---------------------------------------------------------------------------

def verify_osdcs(code, num_seeds=10, trials_per_seed=2000):
    """Run OSD-CS with multiple seeds, return min distance found."""
    seeds = [42, 137, 271, 389, 503, 619, 743, 857, 991, 1103][:num_seeds]
    d_best = code.num_qudits
    results = []
    for seed in seeds:
        d = estimate_distance_noncss(
            code,
            num_trials=trials_per_seed,
            osd_method="osd_cs",
            osd_order=10,
            seed=seed,
        )
        results.append(d)
        d_best = min(d_best, d)
    return d_best, results


# ---------------------------------------------------------------------------
# Tier 3: Symplectic MILP
# ---------------------------------------------------------------------------

def verify_milp(code, timeout_per_logical=60, total_timeout=300):
    """Run symplectic MILP for exact distance."""
    from evaluation.distance_milp import compute_distance_milp_symplectic
    d, details = compute_distance_milp_symplectic(
        code,
        timeout_per_logical=timeout_per_logical,
        total_timeout=total_timeout,
        early_stop=2,
        verbose=True,
    )
    return d, details


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def load_top_codes(jsonl_path, top_n=20, min_fom=10.0):
    """Load and deduplicate top codes from campaign JSONL."""
    codes = []
    with open(jsonl_path) as f:
        for line in f:
            if line.strip():
                codes.append(json.loads(line))

    # Filter by min FOM
    codes = [c for c in codes if c.get("fom", 0) >= min_fom]

    # Deduplicate by (ell, m, A, B, C, D) tuples
    seen = set()
    unique = []
    for c in sorted(codes, key=lambda x: -x.get("fom", 0)):
        key = (
            c.get("ell"), c.get("m"),
            tuple(tuple(t) for t in c["A_terms"]),
            tuple(tuple(t) for t in c["B_terms"]),
            tuple(tuple(t) for t in c.get("C_terms", [])),
            tuple(tuple(t) for t in c.get("D_terms", [])),
        )
        if key not in seen:
            seen.add(key)
            unique.append(c)

    return unique[:top_n]


def main():
    parser = argparse.ArgumentParser(description="Verify Campaign 7d codes")
    parser.add_argument("--jsonl", default="results/evolution/campaign7d/all_codes_noncss.jsonl")
    parser.add_argument("--top", type=int, default=20, help="Number of top codes to verify")
    parser.add_argument("--min-fom", type=float, default=10.0, help="Minimum FOM to consider")
    parser.add_argument("--tier", type=int, default=3, choices=[1, 2, 3], help="Max verification tier")
    parser.add_argument("--milp-timeout", type=int, default=300, help="Total MILP timeout per code (s)")
    parser.add_argument("--osd-seeds", type=int, default=10, help="Number of OSD-CS seeds")
    parser.add_argument("--osd-trials", type=int, default=2000, help="Trials per OSD-CS seed")
    parser.add_argument("--output", default="results/campaign7d_verified.jsonl")
    args = parser.parse_args()

    print(f"Loading codes from {args.jsonl}...")
    top_codes = load_top_codes(args.jsonl, top_n=args.top, min_fom=args.min_fom)
    print(f"Found {len(top_codes)} unique codes with FOM >= {args.min_fom}")
    print()

    results = []

    for idx, c in enumerate(top_codes):
        ell, m = c["ell"], c["m"]
        A = [tuple(t) for t in c["A_terms"]]
        B = [tuple(t) for t in c["B_terms"]]
        C = [tuple(t) for t in c.get("C_terms", [])]
        D = [tuple(t) for t in c.get("D_terms", [])]
        n_orig, k_orig, d_orig = c["n"], c["k"], c["d"]
        fom_orig = c.get("fom", 0)

        print(f"{'='*70}")
        print(f"[{idx+1}/{len(top_codes)}] [[{n_orig},{k_orig},<={d_orig}]] FOM={fom_orig}")
        print(f"  A={A}")
        print(f"  B={B}")
        print(f"  C={C}")
        print(f"  D={D}")

        try:
            code = build_pbb_code(ell, m, A, B, C, D)
        except Exception as e:
            print(f"  BUILD FAILED: {e}")
            continue

        n, k = get_pbb_params_fast(code)
        print(f"  Rebuilt: n={n}, k={k}")
        if k != k_orig:
            print(f"  WARNING: k mismatch ({k} vs {k_orig})")

        result = {
            "ell": ell, "m": m, "n": n, "k": k,
            "A_terms": A, "B_terms": B, "C_terms": C, "D_terms": D,
            "campaign_d": d_orig, "campaign_fom": fom_orig,
        }

        # --- Tier 1: Low-weight check ---
        print(f"  Tier 1: Low-weight check (d<=4)...", end=" ", flush=True)
        t0 = time.time()
        found, d_low = check_low_weight_symplectic(code, max_weight=4)
        t1 = time.time()
        result["tier1_time"] = round(t1 - t0, 1)
        if found:
            print(f"FOUND d<={d_low} ({t1-t0:.1f}s)")
            result["tier1_d"] = d_low
            result["verified_d"] = d_low
            fom = k * d_low * d_low / n if d_low > 0 else 0
            result["verified_fom"] = round(fom, 2)
            print(f"  VERDICT: d<={d_low}, FOM={fom:.2f} (was {fom_orig})")
            results.append(result)
            continue
        else:
            print(f"d>=5 confirmed ({t1-t0:.1f}s)")
            result["tier1_d"] = ">=5"

        if args.tier < 2:
            result["verified_d"] = ">=5"
            results.append(result)
            continue

        # --- Tier 2: OSD-CS multi-seed ---
        print(f"  Tier 2: OSD-CS (order=10, {args.osd_seeds} seeds x {args.osd_trials} trials)...",
              flush=True)
        t0 = time.time()
        d_osd, seed_results = verify_osdcs(
            code, num_seeds=args.osd_seeds, trials_per_seed=args.osd_trials,
        )
        t2 = time.time()
        result["tier2_time"] = round(t2 - t0, 1)
        result["tier2_d"] = d_osd
        result["tier2_seeds"] = seed_results
        print(f"    d<={d_osd} (seeds: {seed_results}) ({t2-t0:.1f}s)")

        if args.tier < 3:
            result["verified_d"] = d_osd
            fom = k * d_osd * d_osd / n if d_osd > 0 else 0
            result["verified_fom"] = round(fom, 2)
            print(f"  VERDICT: d<={d_osd}, FOM={fom:.2f} (was {fom_orig})")
            results.append(result)
            continue

        # --- Tier 3: Symplectic MILP ---
        print(f"  Tier 3: Symplectic MILP (timeout={args.milp_timeout}s)...", flush=True)
        t0 = time.time()
        d_milp, details = verify_milp(
            code,
            timeout_per_logical=60,
            total_timeout=args.milp_timeout,
        )
        t3 = time.time()
        result["tier3_time"] = round(t3 - t0, 1)
        result["tier3_d"] = d_milp
        result["tier3_exact"] = details.get("exact", False)
        result["tier3_logicals_checked"] = details.get("num_logicals_checked", 0)
        result["tier3_logicals_optimal"] = details.get("logicals_optimal", 0)
        exact_tag = "EXACT" if details.get("exact") else "upper bound"
        print(f"    d={'=' if details.get('exact') else '<='}{d_milp} ({exact_tag}, "
              f"{details.get('num_logicals_checked',0)}/{details.get('total_logicals',0)} logicals, "
              f"{t3-t0:.1f}s)")

        # Final verdict: take the minimum across all tiers
        d_final = min(d_osd, d_milp)
        result["verified_d"] = d_final
        fom = k * d_final * d_final / n if d_final > 0 else 0
        result["verified_fom"] = round(fom, 2)
        result["verified_exact"] = details.get("exact", False)
        print(f"  VERDICT: d{'=' if details.get('exact') else '<='}{d_final}, "
              f"FOM={fom:.2f} (was {fom_orig})")

        results.append(result)

    # --- Summary ---
    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    print(f"{'Code':>22}  {'Camp.FOM':>9}  {'Verified d':>10}  {'Ver.FOM':>8}  {'Exact?':>6}")
    print("-" * 65)
    for r in sorted(results, key=lambda x: -x.get("verified_fom", 0)):
        n, k = r["n"], r["k"]
        d_v = r.get("verified_d", "?")
        fom_v = r.get("verified_fom", "?")
        exact = r.get("verified_exact", False)
        d_str = f"={d_v}" if exact else f"<={d_v}"
        fom_str = f"{fom_v:.2f}" if isinstance(fom_v, (int, float)) else fom_v
        print(f"  [[{n},{k},d{d_str}]]  {r['campaign_fom']:>9.2f}  {d_str:>10}  {fom_str:>8}  {'yes' if exact else 'no':>6}")

    # Save results
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        for r in results:
            f.write(json.dumps(r) + "\n")
    print(f"\nResults saved to {output_path}")


if __name__ == "__main__":
    main()
