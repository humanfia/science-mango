#!/usr/bin/env python3
"""Permutation-equivalence dedup of BB codes via the colored Tanner graph.

Groups codes by (n, k), computes the BLISS canonical form of each
code's colored Tanner graph (qubits / X-checks / Z-checks as three
distinct vertex colors), and partitions into permutation-equivalence
classes -- i.e., equivalence under qubit relabeling that preserves the
X- and Z-stabilizer roles.  Compares each class against known
reference codes (Gross, Bravyi, etc.).

The decision is sound and complete for permutation equivalence; it is
strictly narrower than local Clifford or general code equivalence
(see ``evaluation/tanner_equivalence`` for the proof and caveats).

Usage:
    uv run python tests/check_all_equivalences.py
    uv run python tests/check_all_equivalences.py --verbose
"""

import json
import sys
import time
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from evaluation.bb_code import build_bb_code, get_code_params_fast
from evaluation.tanner_equivalence import canonical_hash


# ── Known reference codes ────────────────────────────────────────────
KNOWN_CODES = [
    {"name": "Gross [[144,12,12]]", "ell": 12, "m": 6,
     "A": [(3,0),(0,1),(0,2)], "B": [(0,3),(1,0),(2,0)], "d": 12},
    {"name": "Bravyi [[288,12,18]]", "ell": 12, "m": 12,
     "A": [(3,0),(0,2),(0,7)], "B": [(0,3),(1,0),(2,0)], "d": 18},
    {"name": "[[288,24,12]]", "ell": 12, "m": 12,
     "A": [(6,0),(0,1),(0,2)], "B": [(0,3),(2,0),(4,0)], "d": 12},
    {"name": "[[288,16,12]] Gross at (12,12)", "ell": 12, "m": 12,
     "A": [(3,0),(0,1),(0,2)], "B": [(0,3),(1,0),(2,0)], "d": 12},
    {"name": "[[360,16,14]]", "ell": 15, "m": 12,
     "A": [(3,0),(0,2),(0,4)], "B": [(0,6),(2,0),(4,0)], "d": 14},
    {"name": "[[360,12,24]] bravyi", "ell": 30, "m": 6,
     "A": [(9,0),(0,1),(0,2)], "B": [(0,3),(25,0),(26,0)], "d": 24},
    # Additional known baselines
    {"name": "[[144,8,8]]", "ell": 12, "m": 6,
     "A": [(3,0),(0,1),(0,4)], "B": [(0,3),(1,0),(4,0)], "d": 8},
]


def code_key(c):
    """Unique key for deduplication at polynomial level."""
    return (c["ell"], c["m"],
            tuple(sorted(tuple(t) for t in c["A_terms"])),
            tuple(sorted(tuple(t) for t in c["B_terms"])))


def load_campaign5_codes():
    """Load all Campaign 5 codes from evolution JSONL."""
    jsonl_path = Path(__file__).parent.parent / "results" / "evolution" / "results" / "evolution_codes.jsonl"
    codes = []
    seen = set()
    with open(jsonl_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            c = json.loads(line)
            key = code_key(c)
            if key not in seen:
                seen.add(key)
                codes.append(c)
    return codes


def main():
    verbose = "--verbose" in sys.argv or "-v" in sys.argv
    t_start = time.perf_counter()

    print("=" * 70)
    print("Campaign 5 -- Comprehensive BLISS Equivalence Check")
    print("=" * 70)

    # ── Load codes ────────────────────────────────────────────────────
    campaign_codes = load_campaign5_codes()
    print(f"\nLoaded {len(campaign_codes)} unique Campaign 5 codes")

    # ── Build reference canonical forms ───────────────────────────────
    print("\nBuilding reference canonical forms...")
    ref_canonicals = {}  # (n, k) -> {canonical_hash: ref_name}
    ref_lookup = {}  # canonical_hash -> ref_name

    for ref in KNOWN_CODES:
        code = build_bb_code(ref["ell"], ref["m"], ref["A"], ref["B"])
        n, k = get_code_params_fast(code)
        ch = canonical_hash(code)
        ref_canonicals.setdefault((n, k), {})[ch] = ref["name"]
        ref_lookup[ch] = ref["name"]
        print(f"  {ref['name']}: (n={n}, k={k}) hash={hash(ch) % 10**8:08d}")

    # ── Group campaign codes by (n, k) ────────────────────────────────
    groups = defaultdict(list)
    for c in campaign_codes:
        groups[(c["n"], c["k"])].append(c)

    # ── Process each group ────────────────────────────────────────────
    print(f"\n{'='*70}")
    print(f"Processing {len(groups)} parameter groups...")
    print(f"{'='*70}")

    all_results = {}
    total_equiv_to_known = 0
    total_novel = 0
    total_novel_classes = 0
    novel_codes = []

    for (n, k) in sorted(groups.keys(), key=lambda x: (-x[1], x[0])):
        group = groups[(n, k)]
        best_d = max(c.get("d", 0) for c in group)
        fom = k * best_d * best_d / n if n > 0 else 0

        print(f"\n  [[{n},{k},d<={best_d}]] -- {len(group)} codes (FOM<={fom:.1f})")

        # Build canonical forms for all codes in this group
        class_map = defaultdict(list)  # canonical_hash -> [code_specs]
        build_errors = 0

        for c in group:
            try:
                code = build_bb_code(c["ell"], c["m"], c["A_terms"], c["B_terms"])
                ch = canonical_hash(code)
                class_map[ch].append(c)
            except Exception as e:
                build_errors += 1
                if verbose:
                    print(f"    ERROR building ({c['ell']},{c['m']}): {e}")

        # Match against known references
        equiv_to_known = 0
        novel_classes = 0
        group_novel_codes = []

        for ch, members in class_map.items():
            if ch in ref_lookup:
                ref_name = ref_lookup[ch]
                equiv_to_known += len(members)
                if verbose:
                    print(f"    {len(members)} codes = {ref_name}")
            else:
                novel_classes += 1
                rep = members[0]  # representative
                d_vals = set(m.get("d", 0) for m in members)
                exact_count = sum(1 for m in members
                                  if m.get("d_is_exact") or m.get("stage") == "milp_exact")
                group_novel_codes.extend(members)
                if verbose or len(members) > 1:
                    print(f"    NEW class ({len(members)} codes): "
                          f"({rep['ell']},{rep['m']}) "
                          f"A={rep['A_terms']} B={rep['B_terms']} "
                          f"d={d_vals} ({exact_count} exact)")
                elif novel_classes <= 5:
                    print(f"    NEW: ({rep['ell']},{rep['m']}) "
                          f"A={rep['A_terms']} B={rep['B_terms']} d<={max(d_vals)}")

        if novel_classes > 5 and not verbose:
            print(f"    ... and {novel_classes - 5} more new classes")

        total_equiv_to_known += equiv_to_known
        total_novel += len(group_novel_codes)
        total_novel_classes += novel_classes
        novel_codes.extend(group_novel_codes)

        # Check ref matches for this (n,k) group
        ref_matches = ref_canonicals.get((n, k), {})

        result = {
            "n": n, "k": k, "best_d": best_d, "fom": fom,
            "total_codes": len(group),
            "equivalence_classes": len(class_map),
            "equiv_to_known": equiv_to_known,
            "novel_classes": novel_classes,
            "novel_codes": len(group_novel_codes),
            "build_errors": build_errors,
            "known_refs_at_nk": list(ref_matches.values()),
        }

        # Store novel class representatives
        novel_reps = []
        for ch, members in class_map.items():
            if ch not in ref_lookup:
                rep = members[0]
                novel_reps.append({
                    "ell": rep["ell"], "m": rep["m"],
                    "A_terms": rep["A_terms"], "B_terms": rep["B_terms"],
                    "d": rep.get("d", 0),
                    "d_is_exact": rep.get("d_is_exact", False) or rep.get("stage") == "milp_exact",
                    "fom": rep.get("fom", 0),
                    "class_size": len(members),
                })
        result["novel_representatives"] = novel_reps
        all_results[f"{n}_{k}"] = result

    # ── Summary ───────────────────────────────────────────────────────
    elapsed = time.perf_counter() - t_start
    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    print(f"  Total unique codes:      {len(campaign_codes)}")
    print(f"  Equivalent to known:     {total_equiv_to_known}")
    print(f"  Potentially novel:       {total_novel} codes in {total_novel_classes} equivalence classes")
    print(f"  Time:                    {elapsed:.1f}s")

    # Find best novel codes by FOM
    print(f"\n  Top novel codes by FOM (upper bound):")
    novel_by_fom = []
    for key, result in all_results.items():
        for rep in result.get("novel_representatives", []):
            d = rep.get("d", 0)
            k_val = result["k"]
            n_val = result["n"]
            fom = k_val * d * d / n_val if n_val > 0 and d > 0 else 0
            exact_str = "exact" if rep.get("d_is_exact") else f"d<={d}"
            novel_by_fom.append((fom, n_val, k_val, d, rep["ell"], rep["m"],
                                 rep["A_terms"], rep["B_terms"], exact_str,
                                 rep["class_size"]))

    novel_by_fom.sort(reverse=True)
    for fom, n, k, d, ell, m, A, B, exact_str, cs in novel_by_fom[:20]:
        print(f"    [[{n},{k},{d}]] FOM={fom:.1f} ({exact_str}) "
              f"at ({ell},{m}) class_size={cs}")

    # ── Save results ──────────────────────────────────────────────────
    out_path = Path(__file__).parent.parent / "results" / "campaign5_full_equivalence.json"
    output = {
        "method": "BLISS Tanner graph canonical labeling (igraph)",
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "total_codes": len(campaign_codes),
        "equiv_to_known": total_equiv_to_known,
        "novel_codes": total_novel,
        "novel_classes": total_novel_classes,
        "elapsed_s": elapsed,
        "groups": all_results,
    }
    with open(out_path, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\n  Results saved to {out_path}")


if __name__ == "__main__":
    main()
