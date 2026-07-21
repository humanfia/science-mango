"""Seed solution for non-CSS PTB code evolution campaign.

PTB (Perturbed Two-Block) codes extend CSS bivariate bicycle codes by
adding perturbation polynomials (C, D) to the z-part of block 1.  This
creates genuinely non-CSS codes that can access higher k values with
moderate distance, beating CSS codes at the same block length.

The generate_candidates function returns 4-tuples (A, B, C, D) where
A, B are the base polynomials and C, D are perturbation polynomials.
Commutativity constraint: (A @ D^T + B @ C^T) % 2 must be symmetric.

PTB construction (corrected):
  Block 1: x-part = [A | B], z-part = [D | C]  (D first, C second!)
  Block 2: x-part = [0 | 0], z-part = [B^T | A^T]

Best known PTB codes (corrected construction, BP-OSD verified):
  [[72,12,≤6]] FOM=6.0 — multiple Base2 variants (campaign 7c)
  [[72,10,≤6]] FOM=5.0 — pre-campaign Base2 known codes
  [[36,4,≥3]]  FOM≥1.3 — Base3 at (6,3)

CRITICAL: Many A,B bases produce d=2 codes regardless of C,D perturbation.
The evaluator now includes an explicit weight-2 check (d≤2 → score=0).
"""

from __future__ import annotations

import numpy as np

# ---------------------------------------------------------------------------
# Known PTB codes — BP-OSD verified
# ---------------------------------------------------------------------------
# Each entry: ell, m, A, B, C, D, (expected_n, expected_k, expected_d_upper)

KNOWN_CODES = [
    # --- Campaign 7c evolved codes (corrected construction, verified d≥3) ---
    # Base2 family at (6,6): best FOM=6.0 with k=12
    {
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(3, 0), (3, 3)],
        "D": [(1, 0), (1, 1), (4, 2)],
        "expected": (72, 12, 6),  # d≤6 stable, FOM=6.0
        "name": "[[72,12,≤6]] B2a (campaign 7c best)",
    },
    {
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(1, 5), (4, 5)],
        "D": [(1, 3), (4, 3)],
        "expected": (72, 12, 6),  # d≤6 stable, FOM=6.0
        "name": "[[72,12,≤6]] B2b",
    },
    {
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(2, 5), (4, 4)],
        "D": [(3, 4), (5, 3)],
        "expected": (72, 12, 6),  # d≤6 stable, FOM=6.0
        "name": "[[72,12,≤6]] B2d",
    },
    {
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(0, 3), (1, 5), (2, 1)],
        "D": [(1, 0), (4, 0)],
        "expected": (72, 12, 6),  # d≤6 stable, FOM=6.0
        "name": "[[72,12,≤6]] B2e",
    },
    # Base2 transpose family at (6,6)
    {
        "ell": 6, "m": 6,
        "A": [(2, 1), (3, 4), (4, 4)],
        "B": [(0, 0), (5, 1), (4, 5)],
        "C": [(5, 1), (5, 4)],
        "D": [(0, 4), (2, 1), (4, 1)],
        "expected": (72, 12, 6),  # d≤6 stable, FOM=6.0
        "name": "[[72,12,≤6]] B2T_a",
    },
    {
        "ell": 6, "m": 6,
        "A": [(2, 1), (3, 4), (4, 4)],
        "B": [(0, 0), (5, 1), (4, 5)],
        "C": [(0, 0), (3, 0)],
        "D": [(2, 4), (5, 4)],
        "expected": (72, 12, 6),  # d≤6 stable, FOM=6.0
        "name": "[[72,12,≤6]] B2T_b",
    },
    # --- Pre-campaign Base2 codes (k=10 after fix) ---
    {
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(0, 5), (1, 0)],
        "D": [(0, 0), (1, 0), (4, 0), (5, 5)],
        "expected": (72, 10, 6),  # d≤6, FOM=5.0
        "name": "[[72,10,≤6]] known Base2",
    },
    {
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(5, 4)],
        "D": [(0, 5), (5, 0)],
        "expected": (72, 10, 6),  # d≤6, FOM=5.0
        "name": "[[72,10,≤6]] Base2 v1",
    },
    {
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(1, 0), (4, 4)],
        "D": [(4, 3)],
        "expected": (72, 10, 6),  # d≤6, FOM=5.0
        "name": "[[72,10,≤6]] Base2 minimal C,D",
    },
    # --- (6,3) codes: Base3 family (k=4, d≥3 after fix) ---
    {
        "ell": 6, "m": 3,
        "A": [(0, 1), (3, 2), (4, 1)],
        "B": [(0, 1), (4, 0), (4, 1)],
        "C": [(0, 2), (2, 1)],
        "D": [(0, 2), (1, 1), (2, 1), (3, 1), (4, 0)],
        "expected": (36, 4, 3),  # k=4 after fix
        "name": "[[36,4,≥3]] Base3 a",
    },
    {
        "ell": 6, "m": 3,
        "A": [(0, 1), (3, 2), (4, 1)],
        "B": [(0, 1), (4, 0), (4, 1)],
        "C": [(0, 1), (1, 1), (3, 1), (4, 0), (4, 2)],
        "D": [(0, 0), (4, 1)],
        "expected": (36, 4, 3),  # k=4 after fix
        "name": "[[36,4,≥3]] Base3 b",
    },
]

# Key base (A,B) pairs — CORRECTED CONSTRUCTION VERIFIED
# NOTE: Base1 ([(0,3),(0,4),(3,2)], [(0,2),(2,2),(4,2)]) produces d=2 ALWAYS.
# It is deliberately excluded.
BASE_AB_PAIRS = [
    # Base 2 (6,6): best FOM=6.0, k=10-12 — only known (6,6) base with d≥3
    ([(1, 2), (4, 3), (4, 4)], [(0, 0), (1, 5), (5, 4)]),
    # Base 2 transpose (6,6): same quality, different code families
    ([(2, 1), (3, 4), (4, 4)], [(0, 0), (5, 1), (4, 5)]),
    # Base 3 (6,3): k=4, d≥3 — small but valid non-CSS codes
    ([(0, 1), (3, 2), (4, 1)], [(0, 1), (4, 0), (4, 1)]),
    # Base 4 (6,3): k=4, d≥3 — variant
    ([(0, 1), (3, 2), (4, 1)], [(3, 1), (4, 0), (4, 1)]),
    # Base 3 transposed (3,6): for the (3,6) lattice
    ([(1, 0), (2, 3), (1, 4)], [(1, 0), (0, 4), (1, 4)]),
    # Base 4 transposed (3,6): for the (3,6) lattice
    ([(1, 0), (2, 3), (1, 4)], [(1, 3), (0, 4), (1, 4)]),
    # Base 2 reduced for (3,6): reduce ell-coords mod 3
    ([(1, 2), (1, 3), (1, 4)], [(0, 0), (1, 5), (2, 4)]),
]

# --- CRITICAL: Patterns that produce d=2 or k=0 ---
# Base1 ([(0,3),(0,4),(3,2)], [(0,2),(2,2),(4,2)]): ALWAYS d=2 with any C,D
# Base6 ([(0,1),(2,3),(4,5)], [(1,0),(3,2),(5,4)]): CSS d=2, PTB d=2
# Self-dual C=D: ALWAYS d=2
# Many random A,B bases: d=2 structurally
# Discovering new A,B bases with d≥3 is the key challenge!


# EVOLVE-BLOCK-START
def generate_candidates(
    ell: int, m: int,
) -> list[tuple[list[tuple[int, int]], list[tuple[int, int]],
                list[tuple[int, int]], list[tuple[int, int]]]]:
    """Generate candidate (A, B, C, D) 4-tuples for PTB code evaluation.

    Returns non-CSS PTB codes at the given lattice. Each candidate is
    (A_terms, B_terms, C_terms, D_terms) where A,B are base polynomials
    and C,D are perturbation polynomials.

    Commutativity constraint: (A @ D^T + B @ C^T) % 2 must be symmetric.
    Pre-checked locally before adding candidates to avoid wasting budget.

    CORRECTED CONSTRUCTION: z-part of block 1 is [D | C] (not [C | D]).
    The evaluator now rejects d≤2 codes (explicit weight-2 check, score=0).

    Key patterns (corrected construction):
    - Base2 A=[(1,2),(4,3),(4,4)], B=[(0,0),(1,5),(5,4)] is the ONLY
      known (6,6) base with d≥3.  Commutativity is very restrictive (~0.04%).
    - Best codes have k=12, d≤6, FOM=6.0 (2-3 term C, 2-3 term D)
    - Base3/Base4 at (6,3) produce k=4, d≥3 codes

    AVOID:
    - C = D (self-dual perturbation): ALWAYS d=2
    - C = 0 or D = 0: gives CSS code (no perturbation)
    - Base1 A=[(0,3),(0,4),(3,2)], B=[(0,2),(2,2),(4,2)]: ALWAYS d=2
    - Most random A,B bases: d=2 structurally

    KEY CHALLENGE: Discover new A,B bases with d≥3 non-CSS codes.
    """
    candidates = []
    seen = set()

    def check_commutativity(A, B, C, D) -> bool:
        """Check if (A @ D^T + B @ C^T) % 2 is symmetric."""
        poly = set()
        for ax, ay in A:
            for dx, dy in D:
                term = ((ax - dx) % ell, (ay - dy) % m)
                poly ^= {term}
        for bx, by in B:
            for cx, cy in C:
                term = ((bx - cx) % ell, (by - cy) % m)
                poly ^= {term}

        for x, y in poly:
            if ((-x) % ell, (-y) % m) not in poly:
                return False
        return True

    def _add(A, B, C, D):
        """Add candidate if not duplicate, has non-empty C, D, and commutes."""
        if not C or not D:
            return
        key = (
            tuple(sorted(A)), tuple(sorted(B)),
            tuple(sorted(C)), tuple(sorted(D)),
        )
        if key not in seen:
            # Local commutativity check saves budget
            if check_commutativity(A, B, C, D):
                seen.add(key)
                candidates.append((list(A), list(B), list(C), list(D)))

    # Strategy 1: Known good codes at this lattice
    for code in KNOWN_CODES:
        if code["ell"] == ell and code["m"] == m:
            _add(
                [tuple(t) for t in code["A"]],
                [tuple(t) for t in code["B"]],
                [tuple(t) for t in code["C"]],
                [tuple(t) for t in code["D"]],
            )

    # Strategy 1b: Explicitly add top FOM=10.7 C,D pairs for both bases
    if (ell, m) == (6, 6):
        top_cd_pairs = [
            ([(0, 4), (4, 4), (5, 1)], [(2, 2), (2, 5)]),
            ([(0, 0), (3, 0)], [(2, 4), (5, 4)]),
        ]
        strong_66 = [
            ([(1, 2), (4, 3), (4, 4)], [(0, 0), (1, 5), (5, 4)]),
            ([(2, 1), (3, 4), (4, 4)], [(0, 0), (5, 1), (4, 5)]),
        ]
        for C, D in top_cd_pairs:
            for A, B in strong_66:
                _add(A, B, C, D)
                # Also try swapped
                if C != D:
                    _add(A, B, D, C)

    # Strategy 2: Perturb known C,D by ±1 on each exponent
    for code in KNOWN_CODES:
        if code["ell"] != ell or code["m"] != m:
            continue
        A = [tuple(t) for t in code["A"]]
        B = [tuple(t) for t in code["B"]]
        C_base = [tuple(t) for t in code["C"]]
        D_base = [tuple(t) for t in code["D"]]

        for delta in [-2, -1, 1, 2]:
            # Perturb each C term
            for i in range(len(C_base)):
                for coord in [0, 1]:
                    new_C = list(C_base)
                    cx, cy = C_base[i]
                    if coord == 0:
                        new_C[i] = ((cx + delta) % ell, cy)
                    else:
                        new_C[i] = (cx, (cy + delta) % m)
                    if len(set(new_C)) == len(new_C):
                        _add(A, B, new_C, D_base)

            # Perturb each D term
            for i in range(len(D_base)):
                for coord in [0, 1]:
                    new_D = list(D_base)
                    dx, dy = D_base[i]
                    if coord == 0:
                        new_D[i] = ((dx + delta) % ell, dy)
                    else:
                        new_D[i] = (dx, (dy + delta) % m)
                    if len(set(new_D)) == len(new_D):
                        _add(A, B, C_base, new_D)

    # Strategy 3: Random C,D with known good A,B bases
    rng = np.random.default_rng(42)
    for A_base, B_base in BASE_AB_PAIRS:
        if not all(ax < ell and ay < m for ax, ay in A_base):
            continue
        if not all(bx < ell and by < m for bx, by in B_base):
            continue

        trials = 1700 if (ell, m) == (6, 6) else 700
        for _ in range(trials):
            if (ell, m) == (6, 6):
                num_c = int(rng.choice([2, 2, 2, 3, 3]))
                num_d = int(rng.choice([2, 2, 2, 3, 3]))
            else:
                num_c = int(rng.choice([2, 3, 4]))
                num_d = int(rng.choice([2, 3, 4]))

            C_terms = set()
            while len(C_terms) < num_c:
                C_terms.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
            D_terms = set()
            while len(D_terms) < num_d:
                D_terms.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))

            C_list = sorted(C_terms)
            D_list = sorted(D_terms)
            if C_list == D_list:
                continue
            _add(A_base, B_base, C_list, D_list)

    # Strategy 4: Vary the number of C,D terms around known codes
    for code in KNOWN_CODES:
        if code["ell"] != ell or code["m"] != m:
            continue
        A = [tuple(t) for t in code["A"]]
        B = [tuple(t) for t in code["B"]]
        C_base = [tuple(t) for t in code["C"]]
        D_base = [tuple(t) for t in code["D"]]

        # Add one random term to C
        for cx in range(ell):
            for cy in range(m):
                new_term = (cx, cy)
                if new_term not in C_base:
                    _add(A, B, C_base + [new_term], D_base)
                    if len(candidates) > 2000:
                        break
            if len(candidates) > 2000:
                break

        # Add one random term to D
        for dx in range(ell):
            for dy in range(m):
                new_term = (dx, dy)
                if new_term not in D_base:
                    _add(A, B, C_base, D_base + [new_term])
                    if len(candidates) > 2500:
                        break
            if len(candidates) > 2500:
                break

        # Remove one term from C (if more than 1 term)
        if len(C_base) > 1:
            for i in range(len(C_base)):
                new_C = C_base[:i] + C_base[i+1:]
                _add(A, B, new_C, D_base)

        # Remove one term from D (if more than 1 term)
        if len(D_base) > 1:
            for i in range(len(D_base)):
                new_D = D_base[:i] + D_base[i+1:]
                _add(A, B, C_base, new_D)

    # Strategy 5: Explore new A,B bases
    if (ell, m) == (6, 6):
        strong_cd = [
            ([(0, 0), (3, 0)], [(2, 4), (5, 4)]),
            ([(0, 4), (4, 4), (5, 1)], [(2, 2), (2, 5)]),
            ([(3, 0), (3, 3)], [(1, 0), (1, 1), (4, 2)]),
            ([(1, 5), (4, 5)], [(1, 3), (4, 3)]),
        ]
        seeds = [
            ([(1, 2), (4, 3), (4, 4)], [(0, 0), (1, 5), (5, 4)]),
            ([(2, 1), (3, 4), (4, 4)], [(0, 0), (5, 1), (4, 5)]),
        ]
        # Mutate known good bases (random term replacement)
        for A0, B0 in seeds:
            for _ in range(1500):
                A_new, B_new = list(A0), list(B0)
                A_new[int(rng.integers(0, 3))] = (int(rng.integers(0, 6)), int(rng.integers(0, 6)))
                B_new[int(rng.integers(0, 3))] = (int(rng.integers(0, 6)), int(rng.integers(0, 6)))
                if len(set(A_new)) != 3 or len(set(B_new)) != 3:
                    continue
                C0, D0 = strong_cd[int(rng.integers(0, len(strong_cd)))]
                _add(A_new, B_new, C0, D0)

    # Smaller fully-random exploration for diversity (all lattices)
    for _ in range(1200):
        if len(candidates) > 4000:
            break
        A_new = [(int(rng.integers(0, ell)), int(rng.integers(0, m))) for _ in range(3)]
        B_new = [(int(rng.integers(0, ell)), int(rng.integers(0, m))) for _ in range(3)]
        if len(set(A_new)) != 3 or len(set(B_new)) != 3:
            continue
        nc, nd = int(rng.choice([2, 3])), int(rng.choice([2, 3]))
        C_simple = sorted(list({(int(rng.integers(0, ell)), int(rng.integers(0, m))) for _ in range(nc + 1)})[:nc])
        D_simple = sorted(list({(int(rng.integers(0, ell)), int(rng.integers(0, m))) for _ in range(nd + 1)})[:nd])
        if C_simple and D_simple and C_simple != D_simple:
            _add(A_new, B_new, C_simple, D_simple)

    # Strategy 6: For (3,6) lattice, try transposed versions of (6,3) bases
    if ell == 3 and m == 6:
        base3_T = ([(1, 0), (2, 3), (1, 4)], [(1, 0), (0, 4), (1, 4)])
        base4_T = ([(1, 0), (2, 3), (1, 4)], [(1, 3), (0, 4), (1, 4)])
        for A_b, B_b in [base3_T, base4_T]:
            if all(ax < ell and ay < m for ax, ay in A_b) and \
               all(bx < ell and by < m for bx, by in B_b):
                for _ in range(300):
                    nc = int(rng.choice([2, 3, 4, 5]))
                    nd = int(rng.choice([2, 3, 4, 5]))
                    Ct = set()
                    while len(Ct) < nc:
                        Ct.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
                    Dt = set()
                    while len(Dt) < nd:
                        Dt.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
                    Cl = sorted(Ct)
                    Dl = sorted(Dt)
                    if Cl != Dl:
                        _add(A_b, B_b, Cl, Dl)

    return candidates
# EVOLVE-BLOCK-END
