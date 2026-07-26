"""Extended verification: 1.5M trials on the 3 headline codes.

Runs 3 decoders × 10 batches × 50,000 trials = 1,500,000 total per code.
This is 10× the publication protocol (150k) to test bound stability.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from tests.soak_test import run_soak_test, DECODER_CONFIGS

HEADLINE_CODES = [
    {
        "label": "[[360,40,≤24]] headline",
        "ell": 15, "m": 12,
        "A_terms": [(0, 0), (0, 10), (0, 11)],
        "B_terms": [(0, 0), (5, 0), (10, 0)],
        "claimed_d": 24, "claimed_fom": 64.0,
        "notes": "Best FOM, confirmed at 150k",
    },
    {
        "label": "[[288,32,≤22]] headline",
        "ell": 24, "m": 6,
        "A_terms": [(12, 0), (0, 2), (0, 4)],
        "B_terms": [(0, 3), (10, 0), (20, 0)],
        "claimed_d": 22, "claimed_fom": 53.8,
        "notes": "Best at n=288, d/sqrt(n)=1.30",
    },
    # NOTE: The previous entry [[144,32,≤14]] had A=B (self-dual) which
    # provably has d=2. BP-OSD overestimates distance on A=B codes. Removed.
]


def main():
    results = []
    for code_spec in HEADLINE_CODES:
        result = run_soak_test(
            code_spec,
            num_batches=10,
            trials_per_batch=50_000,
            decoder_configs=DECODER_CONFIGS,
            verbose=True,
        )
        results.append(result)

        # Print stability assessment
        prev_d = code_spec["claimed_d"]
        new_d = result["verified_d"]
        if new_d == prev_d:
            print(f"\n  >>> STABLE: d≤{new_d} confirmed at 1.5M trials (unchanged from 150k)")
        elif new_d < prev_d:
            print(f"\n  >>> TIGHTENED: d≤{prev_d} -> d≤{new_d} at 1.5M trials")
            print(f"      FOM: {code_spec['claimed_fom']:.1f} -> {result['fom_verified']:.1f}")
        else:
            print(f"\n  >>> NOTE: 1.5M minimum ({new_d}) > 150k minimum ({prev_d})")

    # Save
    output = Path("results/extended_verification_1500k.json")
    output.parent.mkdir(parents=True, exist_ok=True)
    with open(output, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {output}")

    # Summary
    print("\n" + "=" * 60)
    print("EXTENDED VERIFICATION SUMMARY (1,500,000 trials per code)")
    print("=" * 60)
    for r in results:
        status = "STABLE" if not r["d_changed"] else "TIGHTENED"
        print(f"  {r['label']:35s}  d≤{r['verified_d']:3d}  FOM={r['fom_verified']:6.1f}  [{status}]")


if __name__ == "__main__":
    main()
