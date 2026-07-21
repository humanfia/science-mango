"""Phase D: Comparative benchmark -- PBB vs Mirror vs CSS.

Systematically compares non-CSS code families using the multi-channel
BP-OSD estimator.  Results are saved to results/benchmark_noncss.json.

Three benchmarks:
1. PBB codes at (6,6) n=72: Re-estimate d for 65 d>2 codes using BP-OSD
   (resolves MILP timeout artifacts).
2. Mirror codes (two parts).  First, reproduce the specific (group, A, B)
   triples from Khesin & Lu (arXiv:2603.05496) Table 1 and re-estimate d
   under our BP-OSD configuration.  Second, sweep three larger abelian
   groups not covered in their Table 1 -- Z6xZ12, Z6xZ20, Z10xZ12 -- by
   random sampling of 3-element (A, B) subsets to surface mirror codes
   with k>0 at larger n.  The sampling is not an exhaustive enumeration:
   the search space at these group orders is C(|G|-1,2)^2 ~ 10^6-10^7
   (group, A, B)-pair candidates, which is well beyond the scope of this
   benchmark.  We use 200 random trials per group with a fixed seed
   (default_rng(42)) as a coverage check rather than a systematic survey
   -- a small expected-yield exploration that documents what the BP-OSD
   estimator returns on a few representative larger-n mirror codes.
3. Clifford equivalence: Run on PBB codes at (6,3) to determine the
   fraction that are genuinely non-CSS (not Clifford-equivalent to CSS).

Usage::

    uv run python tests/benchmark_noncss.py                  # all benchmarks
    uv run python tests/benchmark_noncss.py --ptb-only       # PBB re-estimation
    uv run python tests/benchmark_noncss.py --mirror-only    # mirror codes
    uv run python tests/benchmark_noncss.py --clifford-only  # Clifford analysis
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

# Ensure project root is on sys.path when run as a script
_project_root = str(Path(__file__).resolve().parent.parent)
if _project_root not in sys.path:
    sys.path.insert(0, _project_root)

import numpy as np
from qldpc.codes import QuditCode

from evaluation.bb_code import build_bb_code
from evaluation.clifford_equivalence import is_equivalently_css
from evaluation.distance_bposd_noncss import (
    estimate_distance_noncss,
    estimate_distance_noncss_osdcs,
)
from evaluation.mirror_code import build_mirror_code, get_mirror_params
from evaluation.pbb_code import build_pbb_code

RESULTS_DIR = Path(__file__).resolve().parent.parent / "results"
SURVEY_66 = RESULTS_DIR / "ptb_survey_6x6_milp.json"
SURVEY_63 = RESULTS_DIR / "ptb_survey_6x3.json"


# --- Mirror codes from arXiv:2603.05496 Table 1 ---

MIRROR_CODES = [
    # Small test codes
    {
        "label": "Z3×Z3 [[9,4,?]]",
        "group": (3, 3),
        "A": [(0, 0), (1, 0), (2, 0)],
        "B": [(0, 0), (0, 1), (0, 2)],
    },
    {
        "label": "Z5×Z6 [[30,4,?]]",
        "group": (5, 6),
        "A": [(0, 0), (0, 1), (0, 2)],
        "B": [(0, 0), (1, 0), (3, 1)],
    },
    # Larger codes -- try several A/B combos to find k > 0
    {
        "label": "Z6×Z6 v1 [[36,?,?]]",
        "group": (6, 6),
        "A": [(0, 0), (1, 0), (0, 1)],
        "B": [(0, 0), (0, 1), (1, 0)],
    },
    {
        "label": "Z6×Z6 v2 [[36,?,?]]",
        "group": (6, 6),
        "A": [(0, 0), (1, 0), (2, 0)],
        "B": [(0, 0), (0, 1), (0, 2)],
    },
    {
        "label": "Z6×Z6 v3 [[36,?,?]]",
        "group": (6, 6),
        "A": [(0, 0), (1, 0), (0, 3)],
        "B": [(0, 0), (0, 1), (3, 0)],
    },
    {
        "label": "Z6×Z12 v1 [[72,?,?]]",
        "group": (6, 12),
        "A": [(0, 0), (1, 0), (0, 1)],
        "B": [(0, 0), (0, 1), (2, 0)],
    },
    {
        "label": "Z6×Z12 v2 [[72,?,?]]",
        "group": (6, 12),
        "A": [(0, 0), (1, 0), (0, 3)],
        "B": [(0, 0), (0, 1), (3, 0)],
    },
    {
        "label": "Z6×Z12 v3 [[72,?,?]]",
        "group": (6, 12),
        "A": [(0, 0), (1, 0), (0, 4)],
        "B": [(0, 0), (0, 3), (2, 0)],
    },
    {
        "label": "Z6×Z20 v1 [[120,?,?]]",
        "group": (6, 20),
        "A": [(0, 0), (1, 0), (0, 1)],
        "B": [(0, 0), (0, 1), (2, 0)],
    },
    {
        "label": "Z6×Z20 v2 [[120,?,?]]",
        "group": (6, 20),
        "A": [(0, 0), (1, 0), (0, 5)],
        "B": [(0, 0), (0, 1), (3, 0)],
    },
    {
        "label": "Z6×Z20 v3 [[120,?,?]]",
        "group": (6, 20),
        "A": [(0, 0), (1, 0), (0, 4)],
        "B": [(0, 0), (0, 5), (2, 0)],
    },
    {
        "label": "Z10×Z12 v1 [[120,?,?]]",
        "group": (10, 12),
        "A": [(0, 0), (1, 0), (0, 1)],
        "B": [(0, 0), (0, 1), (2, 0)],
    },
]


def benchmark_ptb_bposd(num_trials: int = 500, osdcs_trials: int = 200) -> list[dict]:
    """Re-estimate d for PBB codes at (6,6) using BP-OSD."""
    if not SURVEY_66.exists():
        print(f"  SKIP: {SURVEY_66} not found")
        return []

    with open(SURVEY_66) as f:
        survey = json.load(f)

    milp_results = survey.get("milp_results", [])
    if not milp_results:
        print("  SKIP: no MILP results in survey file")
        return []

    print(f"  Re-estimating {len(milp_results)} PBB codes at (6,6) n=72 ...")
    results = []

    for i, entry in enumerate(milp_results):
        A = [tuple(t) for t in entry["A_terms"]]
        B = [tuple(t) for t in entry["B_terms"]]
        C = [tuple(t) for t in entry["C_terms"]]
        D = [tuple(t) for t in entry["D_terms"]]
        entry["k"]
        d_milp = entry.get("d")

        try:
            code = build_pbb_code(6, 6, A, B, C, D)
        except Exception as e:
            print(f"    [{i+1}/{len(milp_results)}] Build failed: {e}")
            continue

        k = code.dimension
        if k == 0:
            continue

        t0 = time.time()
        d_osd0 = estimate_distance_noncss(code, num_trials=num_trials, seed=42)
        d_osdcs = estimate_distance_noncss_osdcs(code, num_trials=osdcs_trials, seed=42)
        d_best = min(d_osd0, d_osdcs)
        elapsed = time.time() - t0

        fom = k * d_best**2 / 72.0
        result = {
            "A": A, "B": B, "C": C, "D": D,
            "n": 72, "k": k,
            "d_milp": d_milp,
            "d_osd0": d_osd0,
            "d_osdcs": d_osdcs,
            "d_best": d_best,
            "fom": round(fom, 2),
            "time_s": round(elapsed, 1),
        }
        results.append(result)

        tag = f"MILP={d_milp}" if d_milp else "no MILP"
        print(
            f"    [{i+1}/{len(milp_results)}] [[72,{k}]] "
            f"OSD0≤{d_osd0} OSDCS≤{d_osdcs} ({tag}) "
            f"FOM={fom:.1f} [{elapsed:.1f}s]"
        )

    return results


def benchmark_mirror_codes(num_trials: int = 500, osdcs_trials: int = 200) -> list[dict]:
    """Build and evaluate mirror codes from arXiv:2603.05496."""
    results = []

    for spec in MIRROR_CODES:
        label = spec["label"]
        group = spec["group"]
        A = spec["A"]
        B = spec["B"]

        print(f"  {label} ...")
        try:
            code = build_mirror_code(group, A, B)
        except Exception as e:
            print(f"    Build failed: {e}")
            continue

        n, k = get_mirror_params(code)
        if k == 0:
            print(f"    k=0, skipping")
            continue

        # Clifford equivalence check
        cliff = is_equivalently_css(code)

        t0 = time.time()
        d_osd0 = estimate_distance_noncss(code, num_trials=num_trials, seed=42)
        d_osdcs = estimate_distance_noncss_osdcs(code, num_trials=osdcs_trials, seed=42)
        d_best = min(d_osd0, d_osdcs)
        elapsed = time.time() - t0

        fom = k * d_best**2 / n
        result = {
            "label": label,
            "group": group,
            "A": A, "B": B,
            "n": n, "k": k,
            "d_osd0": d_osd0,
            "d_osdcs": d_osdcs,
            "d_best": d_best,
            "fom": round(fom, 2),
            "is_equivalently_css": cliff["is_css"],
            "clifford_reason": cliff["reason"],
            "num_y_qubits": cliff["num_y_qubits"],
            "time_s": round(elapsed, 1),
        }
        results.append(result)

        css_tag = "equiv-CSS" if cliff["is_css"] else "genuinely non-CSS"
        print(
            f"    [[{n},{k},≤{d_best}]] OSD0≤{d_osd0} OSDCS≤{d_osdcs} "
            f"FOM={fom:.1f} ({css_tag}) [{elapsed:.1f}s]"
        )

    # Random search for mirror codes with k > 0 at larger n.  These three
    # abelian groups are not covered in Khesin-Lu Table 1; we sample
    # 3-element (A, B) subsets at random (200 trials each, seeded
    # default_rng(42)) rather than enumerating exhaustively because the
    # search space C(|G|-1, 2)^2 reaches ~10^6-10^7 pair-candidates per
    # group and most candidates yield k=0.  This is a representative
    # spot-check on the BP-OSD estimator at larger n, not a systematic
    # survey of all mirror codes at these groups.
    for group, label_prefix, max_search in [
            ((6, 12), "Z6×Z12", 200),
            ((6, 20), "Z6×Z20", 200),
            ((10, 12), "Z10×Z12", 200),
    ]:
        print(f"  Searching {label_prefix} for k>0 codes ({max_search} trials) ...")
        rng_search = np.random.default_rng(42)
        found = 0
        for trial in range(max_search):
            a1, a2 = group
            A_cand = [(0, 0)]
            while len(A_cand) < 3:
                elem = (int(rng_search.integers(0, a1)), int(rng_search.integers(0, a2)))
                if elem not in A_cand:
                    A_cand.append(elem)
            B_cand = [(0, 0)]
            while len(B_cand) < 3:
                elem = (int(rng_search.integers(0, a1)), int(rng_search.integers(0, a2)))
                if elem not in B_cand:
                    B_cand.append(elem)

            try:
                code = build_mirror_code(group, A_cand, B_cand)
            except Exception:
                continue
            n_c, k_c = get_mirror_params(code)
            if k_c == 0:
                continue

            found += 1
            cliff = is_equivalently_css(code)

            t0 = time.time()
            d_osd0 = estimate_distance_noncss(code, num_trials=num_trials, seed=42)
            d_osdcs = estimate_distance_noncss_osdcs(code, num_trials=osdcs_trials, seed=42)
            d_best = min(d_osd0, d_osdcs)
            elapsed = time.time() - t0

            fom = k_c * d_best**2 / n_c
            result = {
                "label": f"{label_prefix} search #{found}",
                "group": group, "A": A_cand, "B": B_cand,
                "n": n_c, "k": k_c,
                "d_osd0": d_osd0, "d_osdcs": d_osdcs, "d_best": d_best,
                "fom": round(fom, 2),
                "is_equivalently_css": cliff["is_css"],
                "clifford_reason": cliff["reason"],
                "num_y_qubits": cliff["num_y_qubits"],
                "time_s": round(elapsed, 1),
            }
            results.append(result)

            css_tag = "CSS" if cliff["is_css"] else "non-CSS"
            print(
                f"    #{found} [[{n_c},{k_c},≤{d_best}]] FOM={fom:.1f} ({css_tag}) "
                f"A={A_cand} B={B_cand} [{elapsed:.1f}s]"
            )
            if found >= 10:
                break

        if found == 0:
            print(f"    No k>0 codes found in {max_search} trials")

    # Also include the CSS Gross code as a baseline
    print("  CSS Gross [[72,12,6]] baseline ...")
    bb = build_bb_code(6, 6, [(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)])
    stab = np.array(bb.matrix, dtype=int) % 2
    gross = QuditCode(stab)

    t0 = time.time()
    d_gross = estimate_distance_noncss(gross, num_trials=num_trials, seed=42)
    elapsed = time.time() - t0
    fom_gross = 12 * d_gross**2 / 72.0

    results.append({
        "label": "Gross [[72,12,6]] CSS baseline",
        "n": 72, "k": 12,
        "d_osd0": d_gross, "d_osdcs": d_gross, "d_best": d_gross,
        "fom": round(fom_gross, 2),
        "is_equivalently_css": True,
        "time_s": round(elapsed, 1),
    })
    print(f"    [[72,12,≤{d_gross}]] FOM={fom_gross:.1f} [{elapsed:.1f}s]")

    return results


def benchmark_clifford_equivalence() -> dict:
    """Run Clifford equivalence on PBB codes at (6,3)."""
    if not SURVEY_63.exists():
        print(f"  SKIP: {SURVEY_63} not found")
        return {}

    with open(SURVEY_63) as f:
        survey = json.load(f)

    # Collect all codes from milp_results (top-level)
    all_codes = []
    for entry in survey.get("milp_results", []):
        all_codes.append({
            "A": [tuple(t) for t in entry["A_terms"]],
            "B": [tuple(t) for t in entry["B_terms"]],
            "C": [tuple(t) for t in entry["C_terms"]],
            "D": [tuple(t) for t in entry["D_terms"]],
            "k": entry["k"],
            "d": entry.get("d"),
        })

    if not all_codes:
        print("  SKIP: no PBB codes found in survey")
        return {}

    print(f"  Checking Clifford equivalence for {len(all_codes)} PBB codes at (6,3) ...")

    genuinely_noncss = 0
    equiv_css = 0
    y_support = 0
    constraint_conflict = 0
    errors = 0

    d4_genuinely_noncss = 0
    d4_equiv_css = 0

    for i, entry in enumerate(all_codes):
        try:
            code = build_pbb_code(6, 3, entry["A"], entry["B"], entry["C"], entry["D"])
            if code.dimension == 0:
                continue
            result = is_equivalently_css(code)

            if result["is_css"]:
                equiv_css += 1
                if entry.get("d") == 4:
                    d4_equiv_css += 1
            else:
                genuinely_noncss += 1
                if "Y support" in result["reason"]:
                    y_support += 1
                elif "Constraint conflict" in result["reason"]:
                    constraint_conflict += 1
                if entry.get("d") == 4:
                    d4_genuinely_noncss += 1
        except Exception:
            errors += 1

        if (i + 1) % 500 == 0:
            print(f"    {i+1}/{len(all_codes)} checked ...")

    total_checked = equiv_css + genuinely_noncss
    summary = {
        "total_codes": len(all_codes),
        "total_checked": total_checked,
        "equivalently_css": equiv_css,
        "genuinely_noncss": genuinely_noncss,
        "noncss_y_support": y_support,
        "noncss_constraint_conflict": constraint_conflict,
        "errors": errors,
        "d4_genuinely_noncss": d4_genuinely_noncss,
        "d4_equiv_css": d4_equiv_css,
        "pct_genuinely_noncss": round(100 * genuinely_noncss / max(1, total_checked), 1),
    }

    print(f"\n  Results:")
    print(f"    Equivalently CSS:    {equiv_css}/{total_checked} ({100*equiv_css/max(1,total_checked):.1f}%)")
    print(f"    Genuinely non-CSS:   {genuinely_noncss}/{total_checked} ({100*genuinely_noncss/max(1,total_checked):.1f}%)")
    print(f"      via Y support:     {y_support}")
    print(f"      via constraint:    {constraint_conflict}")
    print(f"    d=4 genuinely non-CSS: {d4_genuinely_noncss}")
    print(f"    d=4 equiv CSS:       {d4_equiv_css}")

    return summary


def main():
    parser = argparse.ArgumentParser(description="Non-CSS comparative benchmark")
    parser.add_argument("--ptb-only", action="store_true", help="Only run PBB re-estimation")
    parser.add_argument("--mirror-only", action="store_true", help="Only run mirror codes")
    parser.add_argument("--clifford-only", action="store_true", help="Only run Clifford analysis")
    parser.add_argument("--trials", type=int, default=500, help="OSD_0 trials per code")
    parser.add_argument("--osdcs-trials", type=int, default=200, help="OSD-CS trials per code")
    args = parser.parse_args()

    run_all = not (args.ptb_only or args.mirror_only or args.clifford_only)

    output = {"timestamp": time.strftime("%Y-%m-%dT%H:%M:%S")}

    if run_all or args.ptb_only:
        print("\n=== Benchmark 1: PBB codes at (6,6) n=72 via BP-OSD ===")
        output["ptb_66"] = benchmark_ptb_bposd(args.trials, args.osdcs_trials)

    if run_all or args.mirror_only:
        print("\n=== Benchmark 2: Mirror codes from arXiv:2603.05496 ===")
        output["mirror"] = benchmark_mirror_codes(args.trials, args.osdcs_trials)

    if run_all or args.clifford_only:
        print("\n=== Benchmark 3: Clifford equivalence on PBB at (6,3) ===")
        output["clifford_63"] = benchmark_clifford_equivalence()

    out_path = RESULTS_DIR / "benchmark_noncss.json"
    with open(out_path, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\nResults saved to {out_path}")

    # Print summary
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)

    if "ptb_66" in output and output["ptb_66"]:
        ptb = output["ptb_66"]
        d_values = [r["d_best"] for r in ptb]
        fom_values = [r["fom"] for r in ptb]
        print(f"\nPBB (6,6) n=72: {len(ptb)} codes")
        print(f"  d range: {min(d_values)}-{max(d_values)}")
        print(f"  FOM range: {min(fom_values):.1f}-{max(fom_values):.1f}")
        best = max(ptb, key=lambda r: r["fom"])
        print(f"  Best: [[72,{best['k']},≤{best['d_best']}]] FOM={best['fom']}")

    if "mirror" in output and output["mirror"]:
        print(f"\nMirror codes: {len(output['mirror'])} evaluated")
        for r in output["mirror"]:
            css_tag = "CSS" if r.get("is_equivalently_css") else "non-CSS"
            print(f"  [[{r['n']},{r['k']},≤{r['d_best']}]] FOM={r['fom']} ({css_tag})")

    if "clifford_63" in output and output["clifford_63"]:
        c = output["clifford_63"]
        print(f"\nClifford equivalence (6,3): {c['pct_genuinely_noncss']}% genuinely non-CSS")
        print(f"  {c['genuinely_noncss']}/{c['total_checked']} non-CSS, {c['equivalently_css']}/{c['total_checked']} equiv-CSS")


if __name__ == "__main__":
    main()
