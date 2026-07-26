"""Seed solution for non-CSS PBB code evolution campaign.

PBB (perturbed bivariate bicycle) codes extend CSS bivariate bicycle codes by
adding perturbation polynomials (C, D) to the z-part of block 1.  This
creates genuinely non-CSS codes that can access higher k values with
moderate distance, beating CSS codes at the same block length.

The generate_candidates function returns 4-tuples (A, B, C, D) where
A, B are the base polynomials and C, D are perturbation polynomials.
Commutativity constraint: (A @ C^T + B @ D^T) % 2 must be symmetric.

PBB construction (paper convention):
  Block 1: x-part = [A | B], z-part = [C | D]  (C left, D right)
  Block 2: x-part = [0 | 0], z-part = [B^T | A^T]

Lattices evaluated: (6,6) n=72, (9,6) n=108, (12,6) n=144,
(15,6) n=180, (30,6) n=360, (6,3)/(3,6) n=36.

Distance: adaptive hash-based exact (d≤6 at n≤216, d≤4 at n>216),
MILP symplectic for higher d, BP-OSD fallback.

Best known PBB codes (MILP-verified distances):
  [[72,12,6]] FOM=6.0 -- Base2 variants + Base7e
  [[72,10,6]] FOM=5.0 -- pre-campaign Base2
  [[36,4,≥3]] FOM≥1.3 -- Base3 at (6,3)

CRITICAL: Many A,B bases produce d=2 codes regardless of C,D perturbation.
The evaluator rejects d≤4 codes (score=0).
"""

from __future__ import annotations

import numpy as np

# ---------------------------------------------------------------------------
# Known PBB codes -- BP-OSD verified
# ---------------------------------------------------------------------------
# Each entry: ell, m, A, B, C, D, (expected_n, expected_k, expected_d_upper)

KNOWN_CODES = [
    # --- Campaign 7c evolved codes (corrected construction, verified d≥3) ---
    # Base2 family at (6,6): best FOM=6.0 with k=12
    {
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(1, 0), (1, 1), (4, 2)],
        "D": [(3, 0), (3, 3)],
        "expected": (72, 12, 6),  # d≤6 stable, FOM=6.0
        "name": "[[72,12,≤6]] B2a (campaign 7c best)",
    },
    {
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(1, 3), (4, 3)],
        "D": [(1, 5), (4, 5)],
        "expected": (72, 12, 6),  # d≤6 stable, FOM=6.0
        "name": "[[72,12,≤6]] B2b",
    },
    {
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(3, 4), (5, 3)],
        "D": [(2, 5), (4, 4)],
        "expected": (72, 12, 6),  # d≤6 stable, FOM=6.0
        "name": "[[72,12,≤6]] B2d",
    },
    {
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(1, 0), (4, 0)],
        "D": [(0, 3), (1, 5), (2, 1)],
        "expected": (72, 12, 6),  # d≤6 stable, FOM=6.0
        "name": "[[72,12,≤6]] B2e",
    },
    # Base2 transpose family at (6,6)
    {
        "ell": 6, "m": 6,
        "A": [(2, 1), (3, 4), (4, 4)],
        "B": [(0, 0), (5, 1), (4, 5)],
        "C": [(0, 4), (2, 1), (4, 1)],
        "D": [(5, 1), (5, 4)],
        "expected": (72, 12, 6),  # d≤6 stable, FOM=6.0
        "name": "[[72,12,≤6]] B2T_a",
    },
    {
        "ell": 6, "m": 6,
        "A": [(2, 1), (3, 4), (4, 4)],
        "B": [(0, 0), (5, 1), (4, 5)],
        "C": [(2, 4), (5, 4)],
        "D": [(0, 0), (3, 0)],
        "expected": (72, 12, 6),  # d≤6 stable, FOM=6.0
        "name": "[[72,12,≤6]] B2T_b",
    },
    # --- Pre-campaign Base2 codes (k=10 after fix) ---
    {
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(0, 0), (1, 0), (4, 0), (5, 5)],
        "D": [(0, 5), (1, 0)],
        "expected": (72, 10, 6),  # d≤6, FOM=5.0
        "name": "[[72,10,≤6]] known Base2",
    },
    {
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(0, 5), (5, 0)],
        "D": [(5, 4)],
        "expected": (72, 10, 6),  # d≤6, FOM=5.0
        "name": "[[72,10,≤6]] Base2 v1",
    },
    {
        "ell": 6, "m": 6,
        "A": [(1, 2), (4, 3), (4, 4)],
        "B": [(0, 0), (1, 5), (5, 4)],
        "C": [(4, 3)],
        "D": [(1, 0), (4, 4)],
        "expected": (72, 10, 6),  # d≤6, FOM=5.0
        "name": "[[72,10,≤6]] Base2 minimal C,D",
    },
    # --- Campaign 7e new base (MILP-verified d=6) ---
    {
        "ell": 6, "m": 6,
        "A": [(2, 1), (3, 1), (4, 4)],
        "B": [(0, 0), (5, 1), (4, 5)],
        "C": [(2, 2), (2, 5)],
        "D": [(0, 4), (4, 4), (5, 1)],
        "expected": (72, 12, 6),  # MILP-verified d=6, FOM=6.0
        "name": "[[72,12,6]] Base7e (MILP-verified)",
    },
    # --- (6,3) codes: Base3 family (k=4, d≥3 after fix) ---
    {
        "ell": 6, "m": 3,
        "A": [(0, 1), (3, 2), (4, 1)],
        "B": [(0, 1), (4, 0), (4, 1)],
        "C": [(0, 2), (1, 1), (2, 1), (3, 1), (4, 0)],
        "D": [(0, 2), (2, 1)],
        "expected": (36, 4, 3),  # k=4 after fix
        "name": "[[36,4,≥3]] Base3 a",
    },
    {
        "ell": 6, "m": 3,
        "A": [(0, 1), (3, 2), (4, 1)],
        "B": [(0, 1), (4, 0), (4, 1)],
        "C": [(0, 0), (4, 1)],
        "D": [(0, 1), (1, 1), (3, 1), (4, 0), (4, 2)],
        "expected": (36, 4, 3),  # k=4 after fix
        "name": "[[36,4,≥3]] Base3 b",
    },
]

# Key base (A,B) pairs -- CORRECTED CONSTRUCTION VERIFIED
# NOTE: Base1 ([(0,3),(0,4),(3,2)], [(0,2),(2,2),(4,2)]) produces d=2 ALWAYS.
# It is deliberately excluded.
BASE_AB_PAIRS = [
    # Base 2 (6,6): best FOM=6.0, k=10-12 -- only known (6,6) base with d≥3
    ([(1, 2), (4, 3), (4, 4)], [(0, 0), (1, 5), (5, 4)]),
    # Base 2 transpose (6,6): same quality, different code families
    ([(2, 1), (3, 4), (4, 4)], [(0, 0), (5, 1), (4, 5)]),
    # Base 7e (6,6): Campaign 7e discovery, MILP-verified d=6
    ([(2, 1), (3, 1), (4, 4)], [(0, 0), (5, 1), (4, 5)]),
    # Base 3 (6,3): k=4, d≥3 -- small but valid non-CSS codes
    ([(0, 1), (3, 2), (4, 1)], [(0, 1), (4, 0), (4, 1)]),
    # Base 4 (6,3): k=4, d≥3 -- variant
    ([(0, 1), (3, 2), (4, 1)], [(3, 1), (4, 0), (4, 1)]),
]

# --- CRITICAL: Patterns that produce d=2 or k=0 ---
# Base1 ([(0,3),(0,4),(3,2)], [(0,2),(2,2),(4,2)]): ALWAYS d=2 with any C,D
# Base6 ([(0,1),(2,3),(4,5)], [(1,0),(3,2),(5,4)]): CSS d=2, PBB d=2
# Self-dual C=D: ALWAYS d=2
# Many random A,B bases: d=2 structurally
# Discovering new A,B bases with d≥3 is the key challenge!


# EVOLVE-BLOCK-START
def generate_candidates(
    ell: int, m: int,
) -> list[tuple[list[tuple[int, int]], list[tuple[int, int]],
                list[tuple[int, int]], list[tuple[int, int]]]]:
    """Generate candidate (A, B, C, D) 4-tuples for PBB code evaluation.

    Returns non-CSS PBB codes at the given lattice. Each candidate is
    (A_terms, B_terms, C_terms, D_terms) where A,B are base polynomials
    and C,D are perturbation polynomials.

    Commutativity constraint: (A @ C^T + B @ D^T) % 2 must be symmetric.
    Pre-checked locally before adding candidates to avoid wasting budget.

    Paper convention: z-part of block 1 is [C | D] (C left, D right).
    The evaluator rejects d≤4 codes (score=0). Distance is adaptive:
    d≤6 exact at n≤216 (hash-based), d≤4 exact at n>216, MILP for rest.

    Lattices: (6,6) n=72, (9,6) n=108, (12,6) n=144, (15,6) n=180,
    (30,6) n=360, (6,3)/(3,6) n=36.

    Key patterns:
    - Base2 A=[(1,2),(4,3),(4,4)], B=[(0,0),(1,5),(5,4)] -- best (6,6) base
    - Base7e A=[(2,1),(3,1),(4,4)], B=[(0,0),(5,1),(4,5)] -- new (6,6) base
    - Both achieve d=6 (MILP-verified), k=12, FOM=6.0
    - For ℓ>6: shift/scale known bases into larger exponent space
    - At n=360: d≥5 codes need MILP (hash only covers d≤4)

    AVOID: C=D (d=2), C=0/D=0 (CSS), Base1 (always d=2).
    KEY CHALLENGE: Discover new A,B bases with d≥5 at any lattice.
    """
    candidates = []
    seen = set()

    def check_commutativity(A, B, C, D) -> bool:
        """Check if (A @ C^T + B @ D^T) % 2 is symmetric."""
        poly = set()
        for ax, ay in A:
            for cx, cy in C:
                term = ((ax - cx) % ell, (ay - cy) % m)
                poly ^= {term}
        for bx, by in B:
            for dx, dy in D:
                term = ((bx - dx) % ell, (by - dy) % m)
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
        # Only use bases valid at this lattice
        if not all(ax < ell and ay < m for ax, ay in A_base):
            continue
        if not all(bx < ell and by < m for bx, by in B_base):
            continue

        # Commutativity pre-check filters most, so attempt many combinations
        for _ in range(1000):
            # Random C: 1-6 terms
            num_c = rng.integers(1, 7)
            C_terms = set()
            while len(C_terms) < num_c:
                cx = int(rng.integers(0, ell))
                cy = int(rng.integers(0, m))
                C_terms.add((cx, cy))
            C_list = sorted(C_terms)

            # Random D: 1-5 terms
            num_d = rng.integers(1, 6)
            D_terms = set()
            while len(D_terms) < num_d:
                dx = int(rng.integers(0, ell))
                dy = int(rng.integers(0, m))
                D_terms.add((dx, dy))
            D_list = sorted(D_terms)

            # Skip if C == D (self-dual trap)
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

    # Strategy 5: Explore new A,B bases with simple C,D
    for ax in range(1, min(ell, 4)):
        for ay in range(1, min(m, 4)):
            for bx in range(1, min(ell, 4)):
                for by in range(1, min(m, 4)):
                    A_new = [(ax, 0), (0, ay), (0, (2*ay) % m)]
                    B_new = [(0, by), (bx, 0), ((2*bx) % ell, 0)]
                    if len(set(A_new)) != 3 or len(set(B_new)) != 3:
                        continue
                    if not all(a < ell and b < m for a, b in A_new):
                        continue
                    if not all(a < ell and b < m for a, b in B_new):
                        continue
                    for cx in range(ell):
                        for cy in range(m):
                            C_simple = [(cx, cy)]
                            for dx in range(ell):
                                for dy in range(m):
                                    D_simple = [(dx, dy)]
                                    if C_simple != D_simple:
                                        _add(A_new, B_new, C_simple, D_simple)
                                    if len(candidates) > 3000: break
                                if len(candidates) > 3000: break
                            if len(candidates) > 3000: break
                        if len(candidates) > 3000: break
                    if len(candidates) > 3000: break
                if len(candidates) > 3000: break
            if len(candidates) > 3000: break
        if len(candidates) > 3000: break

    # Strategy 6: Scale known bases to larger lattices (ℓ > 6)
    # Known bases have x-exponents < 6 -- valid at larger ℓ but don't
    # explore the expanded exponent space.  Generate shifted/scaled variants.
    if ell > 6 and len(candidates) < 3000:
        for A_base, B_base in BASE_AB_PAIRS:
            # Original base is valid at larger ℓ (exponents < 6 < ℓ)
            if not all(ax < ell and ay < m for ax, ay in A_base):
                continue
            if not all(bx < ell and by < m for bx, by in B_base):
                continue

            # 6a: Use original base with random C,D at larger lattice
            for _ in range(500):
                num_c = int(rng.integers(1, 5))
                C_terms = set()
                while len(C_terms) < num_c:
                    C_terms.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
                num_d = int(rng.integers(1, 5))
                D_terms = set()
                while len(D_terms) < num_d:
                    D_terms.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
                C_list, D_list = sorted(C_terms), sorted(D_terms)
                if C_list != D_list:
                    _add(A_base, B_base, C_list, D_list)
                if len(candidates) > 3000:
                    break

            # 6b: Shift x-exponents of A,B into larger space
            for shift in range(1, ell // 3 + 1):
                A_shifted = [((ax + shift) % ell, ay) for ax, ay in A_base]
                B_shifted = [((bx + shift) % ell, by) for bx, by in B_base]
                if len(set(A_shifted)) != 3 or len(set(B_shifted)) != 3:
                    continue
                for _ in range(200):
                    num_c = int(rng.integers(1, 5))
                    C_terms = set()
                    while len(C_terms) < num_c:
                        C_terms.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
                    num_d = int(rng.integers(1, 5))
                    D_terms = set()
                    while len(D_terms) < num_d:
                        D_terms.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
                    C_list, D_list = sorted(C_terms), sorted(D_terms)
                    if C_list != D_list:
                        _add(A_shifted, B_shifted, C_list, D_list)
                    if len(candidates) > 3000:
                        break
                if len(candidates) > 3000:
                    break
            if len(candidates) > 3000:
                break

    # Strategy 7: Explore new bases at larger lattices with spread exponents
    if ell > 6 and len(candidates) < 2500:
        # Try bases with exponents that span the full [0, ℓ) range
        step = max(1, ell // 6)
        for a1 in range(1, min(ell, 4)):
            for a2 in range(step, ell, step):
                for b1 in range(step, ell, step):
                    A_new = [(a1, 1), (a2, 2), ((a1 + a2) % ell, 0)]
                    B_new = [(0, 0), (b1, 1), ((ell - b1) % ell, 2)]
                    if len(set(A_new)) != 3 or len(set(B_new)) != 3:
                        continue
                    if not all(0 <= ax < ell and 0 <= ay < m for ax, ay in A_new):
                        continue
                    if not all(0 <= bx < ell and 0 <= by < m for bx, by in B_new):
                        continue
                    # Simple 1-term C,D to test the base
                    for cx in range(0, ell, max(1, ell // 6)):
                        for dx in range(0, ell, max(1, ell // 6)):
                            C_s = [(cx, 0)]
                            D_s = [(dx, 1)]
                            if C_s != D_s:
                                _add(A_new, B_new, C_s, D_s)
                            if len(candidates) > 3000:
                                break
                        if len(candidates) > 3000: break
                    if len(candidates) > 3000: break
                if len(candidates) > 3000: break
            if len(candidates) > 3000: break

    return candidates
# EVOLVE-BLOCK-END
