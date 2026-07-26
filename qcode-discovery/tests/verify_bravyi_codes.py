"""Re-verify Bravyi et al. (2024) baseline codes under the same 150k-trial
multi-decoder protocol used for our discovered codes.

This addresses the **asymmetric baseline comparison** concern raised during
paper review: if Bravyi et al. codes also tighten under aggressive
multi-decoder verification, the claimed FOM improvement ratios would change.

The script tests three baseline codes:

* ``[[144,12,12]]`` -- the "gross code" (FOM 12.0)
* ``[[288,12,18]]`` -- highest Bravyi et al. FOM at n=288 (FOM 13.5)
* ``[[360,12,<=24]]`` -- highest Bravyi et al. FOM at n=360 (FOM 19.2)

Each code is run through :func:`tests.soak_test.run_soak_test` with the
full 3-decoder x 10-batch x 5000-trial protocol.  Results are saved to
``results/bravyi_verified.json``.

Usage::

    uv run python tests/verify_bravyi_codes.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from tests.soak_test import run_soak_test, DECODER_CONFIGS

BRAVYI_CODES = [
    {
        "label": "[[144,12,12]] Bravyi et al.",
        "ell": 12, "m": 6,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
        "claimed_d": 12, "claimed_fom": 12.0,
        "notes": "Bravyi et al. 2024 gross code",
    },
    {
        "label": "[[288,12,18]] Bravyi et al.",
        "ell": 12, "m": 12,
        "A_terms": [(3, 0), (0, 2), (0, 7)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
        "claimed_d": 18, "claimed_fom": 13.5,
        "notes": "Bravyi et al. 2024",
    },
    {
        "label": "[[360,12,<=24]] Bravyi et al.",
        "ell": 30, "m": 6,
        "A_terms": [(9, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (25, 0), (26, 0)],
        "claimed_d": 24, "claimed_fom": 19.2,
        "notes": "Bravyi et al. 2024",
    },
]


def main():
    results = []
    for code_spec in BRAVYI_CODES:
        result = run_soak_test(
            code_spec,
            num_batches=10,
            trials_per_batch=5000,
            decoder_configs=DECODER_CONFIGS,
            verbose=True,
        )
        results.append(result)
        print(f"\n  RESULT: {result['label']}")
        print(f"    Bravyi et al. claimed: d={code_spec['claimed_d']}, FOM={code_spec['claimed_fom']}")
        print(f"    Verified:              d≤{result['verified_d']}, FOM={result['fom_verified']:.1f}")
        changed = "YES - TIGHTENED" if result['d_changed'] else "NO - UNCHANGED"
        print(f"    Distance changed: {changed}")

    outpath = Path(__file__).resolve().parent.parent / "results" / "bravyi_verified.json"
    with open(outpath, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {outpath}")

    # Summary
    print("\n" + "=" * 70)
    print("  BRAVYI ET AL. BASELINE VERIFICATION SUMMARY")
    print("=" * 70)
    for r in results:
        d_claimed = r["claimed_d"]
        d_ver = r["verified_d"]
        status = "UNCHANGED" if d_claimed == d_ver else f"TIGHTENED: {d_claimed} → {d_ver}"
        print(f"  {r['label']:35s}  d_claimed={d_claimed:3d}  d_verified={d_ver:3d}  {status}")


if __name__ == "__main__":
    main()
