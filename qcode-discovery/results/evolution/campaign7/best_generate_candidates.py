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

Lattices evaluated: (6,6) n=72, (9,6) n=108, (12,6) n=144,
(15,6) n=180, (30,6) n=360, (6,3)/(3,6) n=36.

Distance: adaptive hash-based exact (d≤6 at n≤216, d≤4 at n>216),
MILP symplectic for higher d, BP-OSD fallback.

Best known PTB codes (MILP-verified distances):
  [[72,12,6]] FOM=6.0 — Base2 variants + Base7e
  [[72,10,6]] FOM=5.0 — pre-campaign Base2
  [[36,4,≥3]] FOM≥1.3 — Base3 at (6,3)

CRITICAL: Many A,B bases produce d=2 codes regardless of C,D perturbation.
The evaluator rejects d≤4 codes (score=0).
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
    # --- Campaign 7e new base (MILP-verified d=6) ---
    {
        "ell": 6, "m": 6,
        "A": [(2, 1), (3, 1), (4, 4)],
        "B": [(0, 0), (5, 1), (4, 5)],
        "C": [(0, 4), (4, 4), (5, 1)],
        "D": [(2, 2), (2, 5)],
        "expected": (72, 12, 6),  # MILP-verified d=6, FOM=6.0
        "name": "[[72,12,6]] Base7e (MILP-verified)",
    },
    # --- (9,6) codes: Base8 family (k=8, d≤12, FOM=10.7) ---
    {
        "ell": 9, "m": 6,
        "A": [(3, 0), (0, 1), (0, 2)],
        "B": [(0, 3), (1, 0), (2, 0)],
        "C": [(6, 0)],
        "D": [(6, 4)],
        "expected": (108, 8, 12),
        "name": "[[108,8,≤12]] Base8 a",
    },
    {
        "ell": 9, "m": 6,
        "A": [(3, 0), (0, 1), (0, 2)],
        "B": [(0, 3), (1, 0), (2, 0)],
        "C": [(6, 3)],
        "D": [(6, 1)],
        "expected": (108, 8, 12),
        "name": "[[108,8,≤12]] Base8 b",
    },
    {
        "ell": 9, "m": 6,
        "A": [(3, 0), (0, 1), (0, 2)],
        "B": [(0, 3), (2, 0), (4, 0)],
        "C": [(3, 0)],
        "D": [(6, 4)],
        "expected": (108, 8, 12),
        "name": "[[108,8,≤12]] Base8 c",
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
    # Base 7e (6,6): Campaign 7e discovery, MILP-verified d=6
    ([(2, 1), (3, 1), (4, 4)], [(0, 0), (5, 1), (4, 5)]),
    # Base 3 (6,3): k=4, d≥3 — small but valid non-CSS codes
    ([(0, 1), (3, 2), (4, 1)], [(0, 1), (4, 0), (4, 1)]),
    # Base 4 (6,3): k=4, d≥3 — variant
    ([(0, 1), (3, 2), (4, 1)], [(3, 1), (4, 0), (4, 1)]),
    # Base 8 (9,6): FOM=10.7, k=8 — discovered recently
    ([(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)]),
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
    The evaluator rejects d≤4 codes (score=0). Distance is adaptive:
    d≤6 exact at n≤216 (hash-based), d≤4 exact at n>216, MILP for rest.

    Lattices: (6,6) n=72, (9,6) n=108, (12,6) n=144, (15,6) n=180,
    (30,6) n=360, (6,3)/(3,6) n=36.

    Key patterns:
    - Base2 A=[(1,2),(4,3),(4,4)], B=[(0,0),(1,5),(5,4)] — best (6,6) base
    - Base7e A=[(2,1),(3,1),(4,4)], B=[(0,0),(5,1),(4,5)] — new (6,6) base
    - Both achieve d=6 (MILP-verified), k=12, FOM=6.0
    - For ℓ>6: shift/scale known bases into larger exponent space
    - At n=360: d≥5 codes need MILP (hash only covers d≤4)

    AVOID: C=D (d=2), C=0/D=0 (CSS), Base1 (always d=2).
    KEY CHALLENGE: Discover new A,B bases with d≥5 at any lattice.
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
        # Self-dual perturbation is a known d=2 trap.
        if sorted(C) == sorted(D):
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

    # Strategy 3: Random C,D with known good A,B bases (size-aware, structure-aware)
    rng = np.random.default_rng(42)
    n = 2 * ell * m
    # Favor denser exploration where exact/strong distance checks are available
    base_attempts = 1600 if n <= 216 else 700

    for A_base, B_base in BASE_AB_PAIRS:
        # Only use bases valid at this lattice
        if not all(ax < ell and ay < m for ax, ay in A_base):
            continue
        if not all(bx < ell and by < m for bx, by in B_base):
            continue

        # Structural bias: best large-lattice hits align C,D x-support with A/B x-support
        x_support = sorted({x for x, _ in A_base} | {x for x, _ in B_base})

        for _ in range(base_attempts):
            # Bias toward 2-3 terms (historically best for k>=10 non-CSS PTB)
            num_c = int(rng.choice([2, 2, 3, 3, 4]))
            num_d = int(rng.choice([2, 2, 3, 3, 4]))

            C_terms = set()
            while len(C_terms) < num_c:
                if ell > 6 and rng.random() < 0.7 and x_support:
                    cx = int(rng.choice(x_support))
                else:
                    cx = int(rng.integers(0, ell))
                cy = int(rng.integers(0, m))
                C_terms.add((cx, cy))

            D_terms = set()
            while len(D_terms) < num_d:
                if ell > 6 and rng.random() < 0.7 and x_support:
                    dx = int(rng.choice(x_support))
                else:
                    dx = int(rng.integers(0, ell))
                dy = int(rng.integers(0, m))
                D_terms.add((dx, dy))

            C_list = sorted(C_terms)
            D_list = sorted(D_terms)

            # Self-dual perturbation trap
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

    # Strategy 5: Explore new A,B bases — structured approach
    import itertools
    from math import gcd
    
    # 5a: Scale known (6,6) bases to larger lattices using multipliers
    if ell > 6:
        for A_base, B_base in BASE_AB_PAIRS[:3]:
            if not all(ay < m for _, ay in A_base) or not all(by < m for _, by in B_base):
                continue
            for mult_x in range(1, ell):
                if gcd(mult_x, ell) != 1:
                    continue
                for mult_y in range(1, m):
                    if gcd(mult_y, m) != 1:
                        continue
                    if mult_x == 1 and mult_y == 1:
                        continue
                    A_scaled = [((ax * mult_x) % ell, (ay * mult_y) % m) for ax, ay in A_base]
                    B_scaled = [((bx * mult_x) % ell, (by * mult_y) % m) for bx, by in B_base]
                    if len(set(A_scaled)) != 3 or len(set(B_scaled)) != 3:
                        continue
                    for code in KNOWN_CODES:
                        if code["ell"] != 6 or code["m"] != 6:
                            continue
                        if code["m"] != m:
                            continue
                        C_scaled = [((cx * mult_x) % ell, (cy * mult_y) % m) for cx, cy in code["C"]]
                        D_scaled = [((dx * mult_x) % ell, (dy * mult_y) % m) for dx, dy in code["D"]]
                        if len(set(C_scaled)) == len(C_scaled) and len(set(D_scaled)) == len(D_scaled):
                            _add(A_scaled, B_scaled, C_scaled, D_scaled)
                    for _ in range(100):
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
                            _add(A_scaled, B_scaled, C_list, D_list)

    # 5b: Transpose bases for (3,6) lattice
    if ell == 3 and m == 6:
        base3_A = [(1, 0), (2, 3), (1, 4)]
        base3_B = [(1, 0), (0, 4), (1, 4)]
        for _ in range(500):
            num_c = int(rng.integers(1, 4))
            C_terms = set()
            while len(C_terms) < num_c: C_terms.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
            num_d = int(rng.integers(1, 4))
            D_terms = set()
            while len(D_terms) < num_d: D_terms.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
            C_list, D_list = sorted(C_terms), sorted(D_terms)
            if C_list != D_list: _add(base3_A, base3_B, C_list, D_list)

    # 5c: Simple structured new bases (limited budget)
    if len(candidates) < 3000:
        for ax, ay, bx, by in itertools.product(range(1, min(ell, 4)), range(1, min(m, 4)), range(1, min(ell, 4)), range(1, min(m, 4))):
            if len(candidates) > 3500: break
            A_new = [(ax, 0), (0, ay), (0, (2*ay) % m)]
            B_new = [(0, by), (bx, 0), ((2*bx) % ell, 0)]
            if len(set(A_new)) != 3 or len(set(B_new)) != 3: continue
            if not all(a < ell and b < m for a, b in A_new + B_new): continue
            for _ in range(20):
                c1 = (int(rng.integers(0, ell)), int(rng.integers(0, m)))
                c2 = (int(rng.integers(0, ell)), int(rng.integers(0, m)))
                d1 = (int(rng.integers(0, ell)), int(rng.integers(0, m)))
                d2 = (int(rng.integers(0, ell)), int(rng.integers(0, m)))
                C_l = sorted(set([c1, c2]))
                D_l = sorted(set([d1, d2]))
                if C_l and D_l and C_l != D_l:
                    _add(A_new, B_new, C_l, D_l)

    # Strategy 6: Scale known bases to larger lattices (ℓ > 6)
    if ell > 6 and len(candidates) < 4200:
        from math import gcd

        for A_base, B_base in BASE_AB_PAIRS[:3]:
            if not all(ax < ell and ay < m for ax, ay in A_base):
                continue
            if not all(bx < ell and by < m for bx, by in B_base):
                continue

            # 6a) Multiplicative x-scaling (very important at ell=30)
            for mult_x in range(1, ell):
                if gcd(mult_x, ell) != 1:
                    continue
                A_sc = [((ax * mult_x) % ell, ay) for ax, ay in A_base]
                B_sc = [((bx * mult_x) % ell, by) for bx, by in B_base]
                if len(set(A_sc)) != 3 or len(set(B_sc)) != 3:
                    continue

                ax_coords = sorted({x for x, _ in A_sc})
                for _ in range(180):
                    # Emulate successful |C|=|D|=2 families with A-aligned x coords
                    c1x = int(rng.choice(ax_coords))
                    c2x = int(rng.choice(ax_coords))
                    d1x = int(rng.choice(ax_coords))
                    d2x = int(rng.choice(ax_coords))
                    C_list = sorted(set([(c1x, int(rng.integers(0, m))), (c2x, int(rng.integers(0, m)))]))
                    D_list = sorted(set([(d1x, int(rng.integers(0, m))), (d2x, int(rng.integers(0, m)))]))
                    if C_list and D_list and C_list != D_list:
                        _add(A_sc, B_sc, C_list, D_list)

            # 6b) Additive x-shifts
            for shift in range(1, ell // 2 + 1):
                A_shifted = [((ax + shift) % ell, ay) for ax, ay in A_base]
                B_shifted = [((bx + shift) % ell, by) for bx, by in B_base]
                if len(set(A_shifted)) != 3 or len(set(B_shifted)) != 3:
                    continue

                x_support = sorted({x for x, _ in A_shifted} | {x for x, _ in B_shifted})
                for _ in range(120):
                    num_c = int(rng.choice([2, 2, 3, 3]))
                    num_d = int(rng.choice([2, 2, 3, 3]))
                    C_terms, D_terms = set(), set()
                    while len(C_terms) < num_c:
                        cx = int(rng.choice(x_support)) if rng.random() < 0.7 else int(rng.integers(0, ell))
                        C_terms.add((cx, int(rng.integers(0, m))))
                    while len(D_terms) < num_d:
                        dx = int(rng.choice(x_support)) if rng.random() < 0.7 else int(rng.integers(0, ell))
                        D_terms.add((dx, int(rng.integers(0, m))))
                    C_list, D_list = sorted(C_terms), sorted(D_terms)
                    if C_list != D_list:
                        _add(A_shifted, B_shifted, C_list, D_list)

    # Strategy 7: Explore new bases at larger lattices with spread exponents
    if ell > 6 and len(candidates) < 4500:
        step = max(1, ell // 6)
        for a1 in range(1, min(ell, 5)):
            for a2 in range(ell//3, ell, step):
                if a1 == a2: continue
                for b1 in range(1, min(ell, 5)):
                    for b2 in range(ell//3, ell, step):
                        A_new = [(a1, 2), (a2, 3), (a2, 4)]
                        B_new = [(0, 0), (b1, 5 % m), (b2, 4)]
                        if m <= 4:
                            A_new = [(a1, 1), (a2, 2), (a2, 0)]
                            B_new = [(0, 0), (b1, 2 % m), (b2, 1)]
                        if len(set(A_new)) != 3 or len(set(B_new)) != 3: continue
                        if not all(0 <= ax < ell and 0 <= ay < m for ax, ay in A_new): continue
                        if not all(0 <= bx < ell and 0 <= by < m for bx, by in B_new): continue
                        for _ in range(15):
                            c1 = (int(rng.integers(0, ell)), int(rng.integers(0, m)))
                            c2 = (int(rng.integers(0, ell)), int(rng.integers(0, m)))
                            d1 = (int(rng.integers(0, ell)), int(rng.integers(0, m)))
                            d2 = (int(rng.integers(0, ell)), int(rng.integers(0, m)))
                            C_l = sorted(set([c1, c2]))
                            D_l = sorted(set([d1, d2]))
                            if C_l and D_l and C_l != D_l:
                                _add(A_new, B_new, C_l, D_l)

    # Strategy 8: Cross-pollinate C,D between known codes
    if ell == 6 and m == 6:
        code_list = [c for c in KNOWN_CODES if c["ell"] == 6 and c["m"] == 6]
        for i, c1 in enumerate(code_list):
            for j, c2 in enumerate(code_list):
                if i == j: continue
                A = [tuple(t) for t in c1["A"]]
                B = [tuple(t) for t in c1["B"]]
                C = [tuple(t) for t in c1["C"]]
                D = [tuple(t) for t in c2["D"]]
                _add(A, B, C, D)
                C2 = [tuple(t) for t in c2["C"]]
                D2 = [tuple(t) for t in c1["D"]]
                _add(A, B, C2, D2)

    return candidates
# EVOLVE-BLOCK-END
