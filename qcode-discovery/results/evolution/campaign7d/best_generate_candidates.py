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
    # --- Base5 "diagonal" family at (6,6): BREAKTHROUGH k=16, d≤8, FOM=14.22 ---
    {
        "ell": 6, "m": 6,
        "A": [(1, 0), (2, 1), (3, 2)],
        "B": [(0, 3), (0, 5), (3, 4)],
        "C": [(0, 4)],
        "D": [(5, 1)],
        "expected": (72, 16, 8),  # FOM=14.22
        "name": "[[72,16,≤8]] B5a (breakthrough)",
    },
    {
        "ell": 6, "m": 6,
        "A": [(1, 0), (2, 1), (3, 2)],
        "B": [(0, 3), (0, 5), (3, 4)],
        "C": [(0, 3), (2, 3), (5, 2)],
        "D": [(2, 3), (4, 1)],
        "expected": (72, 16, 8),  # FOM=14.22
        "name": "[[72,16,≤8]] B5b",
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
    # Base 5 "diagonal" (6,6): BREAKTHROUGH k=16, d≤8, FOM=14.22!
    ([(1, 0), (2, 1), (3, 2)], [(0, 3), (0, 5), (3, 4)]),
    # Base 3 (6,3): k=4, d≥3 — small but valid non-CSS codes
    ([(0, 1), (3, 2), (4, 1)], [(0, 1), (4, 0), (4, 1)]),
    # Base 4 (6,3): k=4, d≥3 — variant
    ([(0, 1), (3, 2), (4, 1)], [(3, 1), (4, 0), (4, 1)]),
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

    # Strategy 2b: Intensively explore around the d≤8 winners
    if ell == 6 and m == 6:
        A_b5 = [(1,0),(2,1),(3,2)]
        B_b5 = [(0,3),(0,5),(3,4)]
        A_b2t = [(2,1),(3,4),(4,4)]
        B_b2t = [(0,0),(5,1),(4,5)]
        A_b2 = [(1,2),(4,3),(4,4)]
        B_b2 = [(0,0),(1,5),(5,4)]
        
        # These achieved [[72,12,≤8]] FOM=10.67 — explore neighbors
        d8_winners = [
            (A_b5, B_b5, [(0,4)], [(5,1)]),
            (A_b5, B_b5, [(0,3),(2,3),(5,2)], [(2,3),(4,1)]),
            (A_b2t, B_b2t, [(0,0),(3,0)], [(2,4),(5,4)]),
            (A_b2t, B_b2t, [(0,4),(4,4),(5,1)], [(2,2),(2,5)]),
            (A_b2, B_b2, [(3,0),(3,3)], [(1,0),(1,1),(4,2)]),
        ]
        
        # All known good C,D pairs for cross-pollination
        good_Cs = [
            [(0,0),(3,0)], [(0,4),(4,4),(5,1)], [(5,1),(5,4)],
            [(3,0),(3,3)], [(1,5),(4,5)], [(2,5),(4,4)],
            [(0,3),(1,5),(2,1)], [(0,5),(1,0)], [(5,4)], [(1,0),(4,4)],
        ]
        good_Ds = [
            [(2,4),(5,4)], [(2,2),(2,5)], [(0,4),(2,1),(4,1)],
            [(1,0),(1,1),(4,2)], [(1,3),(4,3)], [(3,4),(5,3)],
            [(1,0),(4,0)], [(0,0),(1,0),(4,0),(5,5)], [(0,5),(5,0)], [(4,3)],
        ]
        
        # Cross-pollinate: try all C from winners with all D from winners
        for base_A, base_B in [(A_b2t, B_b2t), (A_b2, B_b2)]:
            for gc in good_Cs:
                for gd in good_Ds:
                    if gc != gd:
                        _add(base_A, base_B, gc, gd)
        
        for A_w, B_w, C_w, D_w in d8_winners:
            # Simultaneous perturbation of both C and D
            for delta_c in [-2, -1, 1, 2]:
                for delta_d in [-2, -1, 1, 2]:
                    for ic in range(len(C_w)):
                        for id_ in range(len(D_w)):
                            for cc in [0, 1]:
                                for dc in [0, 1]:
                                    nc = list(C_w)
                                    nd = list(D_w)
                                    cx, cy = C_w[ic]
                                    dx, dy = D_w[id_]
                                    nc[ic] = ((cx+delta_c)%ell, cy) if cc==0 else (cx, (cy+delta_c)%m)
                                    nd[id_] = ((dx+delta_d)%ell, dy) if dc==0 else (dx, (dy+delta_d)%m)
                                    if len(set(nc))==len(nc) and len(set(nd))==len(nd):
                                        _add(A_w, B_w, nc, nd)
            # Swap C and D (asymmetric exploration)
            _add(A_w, B_w, D_w, C_w)
            # Add/remove terms — exhaustive for small lattice
            for cx in range(ell):
                for cy in range(m):
                    t = (cx, cy)
                    if t not in C_w:
                        _add(A_w, B_w, C_w + [t], D_w)
                    if t not in D_w:
                        _add(A_w, B_w, C_w, D_w + [t])
                    # Remove + add (substitution)
                    for i in range(len(C_w)):
                        if t not in C_w:
                            nc = C_w[:i] + C_w[i+1:] + [t]
                            if len(set(nc)) == len(nc):
                                _add(A_w, B_w, nc, D_w)
                    for i in range(len(D_w)):
                        if t not in D_w:
                            nd = D_w[:i] + D_w[i+1:] + [t]
                            if len(set(nd)) == len(nd):
                                _add(A_w, B_w, C_w, nd)
            # Remove terms
            if len(C_w) > 1:
                for i in range(len(C_w)):
                    _add(A_w, B_w, C_w[:i]+C_w[i+1:], D_w)
            if len(D_w) > 1:
                for i in range(len(D_w)):
                    _add(A_w, B_w, C_w, D_w[:i]+D_w[i+1:])

    # Strategy 3: Random C,D with known good A,B bases (multiple seeds)
    for seed in [42, 137, 271, 503, 719]:
        rng = np.random.default_rng(seed)
        for A_base, B_base in BASE_AB_PAIRS:
            # Only use bases valid at this lattice
            if not all(ax < ell and ay < m for ax, ay in A_base):
                continue
            if not all(bx < ell and by < m for bx, by in B_base):
                continue

            # Commutativity pre-check filters most, so attempt many combinations
            for _ in range(1000):
                # Random C: 1-6 terms
                num_c = int(rng.choice([1, 2, 2, 2, 3, 3, 4, 5, 6]))
                C_terms = set()
                while len(C_terms) < num_c:
                    cx = int(rng.integers(0, ell))
                    cy = int(rng.integers(0, m))
                    C_terms.add((cx, cy))
                C_list = sorted(C_terms)

                # Random D: 1-5 terms
                num_d = int(rng.choice([1, 2, 2, 2, 3, 3, 4, 5]))
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
    rng = np.random.default_rng(42)

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

    # Strategy 5: Perturb known A,B bases (Search for new bases)
    for code in KNOWN_CODES:
        if code["ell"] != ell or code["m"] != m:
            continue
        A_base = [tuple(t) for t in code["A"]]
        B_base = [tuple(t) for t in code["B"]]
        C = [tuple(t) for t in code["C"]]
        D = [tuple(t) for t in code["D"]]
        
        for delta in [-1, 1]:
            # Perturb each A term
            for i in range(len(A_base)):
                for coord in [0, 1]:
                    new_A = list(A_base)
                    ax, ay = A_base[i]
                    if coord == 0:
                        new_A[i] = ((ax + delta) % ell, ay)
                    else:
                        new_A[i] = (ax, (ay + delta) % m)
                    if len(set(new_A)) == len(new_A):
                        _add(new_A, B_base, C, D)
            
            # Perturb each B term
            for i in range(len(B_base)):
                for coord in [0, 1]:
                    new_B = list(B_base)
                    bx, by = B_base[i]
                    if coord == 0:
                        new_B[i] = ((bx + delta) % ell, by)
                    else:
                        new_B[i] = (bx, (by + delta) % m)
                    if len(set(new_B)) == len(new_B):
                        _add(A_base, new_B, C, D)

    # Strategy 6: Lattice Automorphisms (scaling and swapping) of known good bases
    for code in KNOWN_CODES:
        if code["ell"] != ell or code["m"] != m:
            continue
        A_base = [tuple(t) for t in code["A"]]
        B_base = [tuple(t) for t in code["B"]]
        C = [tuple(t) for t in code["C"]]
        D = [tuple(t) for t in code["D"]]
        
        # Coprimes for scaling
        scales_x = [1, 5] if ell == 6 else ([1, 2] if ell == 3 else [1])
        scales_y = [1, 5] if m == 6 else ([1, 2] if m == 3 else [1])
        
        for sx in scales_x:
            for sy in scales_y:
                if sx == 1 and sy == 1:
                    continue
                # Apply scaling
                nA = list(set(((ax * sx) % ell, (ay * sy) % m) for ax, ay in A_base))
                nB = list(set(((bx * sx) % ell, (by * sy) % m) for bx, by in B_base))
                nC = list(set(((cx * sx) % ell, (cy * sy) % m) for cx, cy in C))
                nD = list(set(((dx * sx) % ell, (dy * sy) % m) for dx, dy in D))
                if len(nA) == len(A_base) and len(nB) == len(B_base):
                    _add(nA, nB, nC, nD)
                
                # Apply axis swap if square lattice
                if ell == m:
                    nAs = list(set((y, x) for x, y in nA))
                    nBs = list(set((y, x) for x, y in nB))
                    nCs = list(set((y, x) for x, y in nC))
                    nDs = list(set((y, x) for x, y in nD))
                    if len(nAs) == len(A_base) and len(nBs) == len(B_base):
                        _add(nAs, nBs, nCs, nDs)

    # Strategy 7: Random search for entirely new A,B bases (constrained volume)
    if len(candidates) < 4000:
        for _ in range(800):
            A_new = set()
            while len(A_new) < 3:
                A_new.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
            B_new = {(0, 0)}  # Anchor B to (0,0) to reduce symmetry duplicates
            while len(B_new) < 3:
                B_new.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
            A_list, B_list = sorted(A_new), sorted(B_new)
            
            for _ in range(15):
                nc = int(rng.choice([2, 3]))
                nd = int(rng.choice([1, 2, 3]))
                C_t, D_t = set(), set()
                while len(C_t) < nc:
                    C_t.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
                while len(D_t) < nd:
                    D_t.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
                cl, dl = sorted(C_t), sorted(D_t)
                if cl != dl:
                    _add(A_list, B_list, cl, dl)

    return candidates
# EVOLVE-BLOCK-END
