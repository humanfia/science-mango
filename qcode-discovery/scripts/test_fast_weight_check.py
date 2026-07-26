#!/usr/bin/env python3
"""Smoke-test of has_low_weight_logical (symplectic) on known PBB codes.

Originally compared a pure-X/Z-channels variant against the symplectic
hash-based variant; the pure-channel variant has been retired (it was
strictly subsumed by the symplectic version), so this script now just
exercises the symplectic check on the same fixtures.
"""

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from evaluation.pbb_code import build_pbb_code, get_pbb_params_fast
from evaluation.distance_bposd_noncss import has_low_weight_logical

TEST_CODES = [
    # Base2a: known d=6 (MILP-verified), k=12
    {
        "name": "Base2a [[72,12,6]]",
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(3, 0), (3, 3)],
        "D": [(1, 0), (1, 1), (4, 2)],
        "expected_d": 6,
    },
    # Base2b: known d=6, k=12
    {
        "name": "Base2b [[72,12,6]]",
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(1, 5), (4, 5)],
        "D": [(1, 3), (4, 3)],
        "expected_d": 6,
    },
    # Base2 minimal: k=10, d=6
    {
        "name": "Base2 minimal [[72,10,6]]",
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(1, 0), (4, 4)],
        "D": [(4, 3)],
        "expected_d": 6,
    },
]


def main():
    for tc in TEST_CODES:
        print(f"\n{'=' * 60}")
        print(f"Testing: {tc['name']}")
        code = build_pbb_code(
            tc["ell"], tc["m"],
            tc["A"], tc["B"],
            tc.get("C", []), tc.get("D", []),
        )
        n, k = get_pbb_params_fast(code)
        print(f"  n={n}, k={k}")

        t0 = time.time()
        found, d = has_low_weight_logical(code, max_weight=6)
        elapsed = time.time() - t0
        print(f"  symplectic d<=6: found={found}, d={d} ({elapsed:.2f}s)")

        if "expected_d" in tc:
            if found and d == tc["expected_d"]:
                print(f"  PASS: found d={d} == expected d={tc['expected_d']}")
            elif found and d < tc["expected_d"]:
                print(f"  FOUND LOWER: d={d} < expected d={tc['expected_d']} (check!)")
            elif not found:
                print(f"  NOT FOUND: d>6, expected d={tc['expected_d']}")
            else:
                print(f"  d={d}, expected d={tc['expected_d']}")

    print(f"\n{'=' * 60}")
    print("Done!")


if __name__ == "__main__":
    main()
