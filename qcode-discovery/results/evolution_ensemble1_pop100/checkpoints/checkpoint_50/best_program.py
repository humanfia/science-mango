"""Seed solutions for the evolutionary search.

Contains known BB codes from the literature and an initial
generate_candidates() function that the evolutionary loop will mutate.

Sources:
- Bravyi et al. 2024 (arXiv:2308.07915, Table 3)
- qldpc examples (bivariate_bicycle_codes.ipynb)
- Chengyu et al. 2026 (arXiv:2601.18562) — codes referenced by [[n,k]] only;
  exact polynomials to be determined via search.
"""

from __future__ import annotations

# ---------------------------------------------------------------------------
# Known BB codes — verified against qldpc (n, k match exactly)
# ---------------------------------------------------------------------------
# Each entry: ell, m, A_terms, B_terms, (expected_n, expected_k, expected_d, fom)
#
# A_terms / B_terms are lists of (x_exp, y_exp) exponent pairs.
# Polynomial: A = sum of x^a * y^b for each (a,b) in A_terms.
#
# Pattern key:
#   "xy_swap" = A uses x^a + y-terms, B uses y^d + x-terms
#   "mixed"   = A and B don't follow the swap pattern

KNOWN_CODES = [
    # --- arXiv:2308.07915, Table 3 ---
    # [[72, 12, 6]]  A = x^3 + y + y^2, B = y^3 + x + x^2
    {
        "ell": 6, "m": 6,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
        "expected": (72, 12, 6, 6.0),
        "name": "[[72,12,6]]",
        "source": "arXiv:2308.07915",
    },
    # [[90, 8, 10]]  A = x^9 + y + y^2, B = 1 + x^2 + x^7
    {
        "ell": 15, "m": 3,
        "A_terms": [(9, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 0), (2, 0), (7, 0)],
        "expected": (90, 8, 10, 8.89),
        "name": "[[90,8,10]]",
        "source": "arXiv:2308.07915",
    },
    # [[108, 8, 10]]  A = x^3 + y + y^2, B = y^3 + x + x^2
    {
        "ell": 9, "m": 6,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
        "expected": (108, 8, 10, 7.41),
        "name": "[[108,8,10]]",
        "source": "arXiv:2308.07915",
    },
    # [[144, 12, 12]]  A = x^3 + y + y^2, B = y^3 + x + x^2  (the "gross code")
    {
        "ell": 12, "m": 6,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
        "expected": (144, 12, 12, 12.0),
        "name": "[[144,12,12]] gross",
        "source": "arXiv:2308.07915",
    },
    # [[144, 12, 12]]  Same polynomials, different lattice (6,12)
    {
        "ell": 6, "m": 12,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
        "expected": (144, 12, 12, 12.0),
        "name": "[[144,12,12]] (6,12)",
        "source": "arXiv:2308.07915",
    },
    # [[216, 12, ?]]  A = x^3 + y + y^2, B = y^3 + x + x^2
    {
        "ell": 18, "m": 6,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
        "expected": (216, 12, None, None),
        "name": "[[216,12,?]]",
        "source": "arXiv:2308.07915",
    },
    # [[288, 12, 18]]  A = x^3 + y^2 + y^7, B = y^3 + x + x^2
    {
        "ell": 12, "m": 12,
        "A_terms": [(3, 0), (0, 2), (0, 7)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
        "expected": (288, 12, 18, 13.5),
        "name": "[[288,12,18]]",
        "source": "arXiv:2308.07915",
    },
    # [[288, 12, ?]]  A = x^3 + y + y^2, B = y^3 + x + x^2 at (24,6)
    {
        "ell": 24, "m": 6,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
        "expected": (288, 12, None, None),
        "name": "[[288,12,?]] (24,6)",
        "source": "arXiv:2308.07915",
    },
    # [[360, 12, <=24]]  A = x^9 + y + y^2, B = y^3 + x^25 + x^26
    {
        "ell": 30, "m": 6,
        "A_terms": [(9, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (25, 0), (26, 0)],
        "expected": (360, 12, 24, 19.2),
        "name": "[[360,12,<=24]]",
        "source": "arXiv:2308.07915",
    },
    # --- Verified discoveries (150k-trial multi-decoder protocol) ---
    # [[360, 40, <=20]]  Constant-monomial: A = 1+y+y^2, B = 1+x^5+x^10
    {
        "ell": 15, "m": 12,
        "A_terms": [(0, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 0), (5, 0), (10, 0)],
        "expected": (360, 40, 20, 44.4),
        "name": "[[360,40,<=20]]",
        "source": "this work",
    },
    # [[288, 32, <=20]]  x/y-swap: A = x^3+y^2+y^10, B = y^6+x+x^11
    {
        "ell": 12, "m": 12,
        "A_terms": [(3, 0), (0, 2), (0, 10)],
        "B_terms": [(0, 6), (1, 0), (11, 0)],
        "expected": (288, 32, 20, 44.4),
        "name": "[[288,32,<=20]]",
        "source": "this work",
    },
    # [[360, 32, <=16]]  Constant-monomial: A = 1+y^2+y^4, B = 1+x^3+x^4
    {
        "ell": 15, "m": 12,
        "A_terms": [(0, 0), (0, 2), (0, 4)],
        "B_terms": [(0, 0), (3, 0), (4, 0)],
        "expected": (360, 32, 16, 22.8),
        "name": "[[360,32,<=16]]",
        "source": "this work",
    },
    # [[288, 32, <=12]]  Constant-monomial: A = 1+y^2+y^4, B = 1+x^2+x^4
    {
        "ell": 12, "m": 12,
        "A_terms": [(0, 0), (0, 2), (0, 4)],
        "B_terms": [(0, 0), (2, 0), (4, 0)],
        "expected": (288, 32, 12, 16.0),
        "name": "[[288,32,<=12]]",
        "source": "this work",
    },
    # [[288, 24, <=12]]  x/y-swap: A = x^6+y+y^2, B = y^3+x^2+x^4
    {
        "ell": 24, "m": 6,
        "A_terms": [(6, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (2, 0), (4, 0)],
        "expected": (288, 24, 12, 12.0),
        "name": "[[288,24,<=12]]",
        "source": "this work",
    },
]


# Target lattice dimensions for the search
TARGET_LATTICES = [
    # n=144: ell*m = 72
    (12, 6), (6, 12), (9, 8), (8, 9), (24, 3), (36, 2),
    # n=200: ell*m = 100
    (10, 10), (20, 5), (25, 4), (50, 2),
    # n=288: ell*m = 144
    (12, 12), (16, 9), (18, 8), (24, 6),
    # n=360: ell*m = 180
    (15, 12), (18, 10), (20, 9), (30, 6),
]


# EVOLVE-BLOCK-START
def generate_candidates(
    ell: int, m: int
) -> list[tuple[list[tuple[int, int]], list[tuple[int, int]]]]:
    """Generate candidate (A_terms, B_terms) pairs for given lattice dimensions."""
    candidates = []
    seen = set()

    import math

    def _add(a_terms, b_terms):
        """Add candidate if not a duplicate."""
        # Canonicalize: sort terms
        key = (tuple(sorted(a_terms)), tuple(sorted(b_terms)))
        if key not in seen:
            seen.add(key)
            candidates.append((list(a_terms), list(b_terms)))

    # -----------------------------------------------------------------------
    # Helpers
    # -----------------------------------------------------------------------
    def get_units(n):
        """Return list of units modulo n."""
        return [i for i in range(1, n) if math.gcd(i, n) == 1]

    def get_doubling_pairs(n):
        """Return pairs (u, 2u) for u in units."""
        pairs = []
        for u in get_units(n):
            v = (2 * u) % n
            if v != 0 and v != u:
                pairs.append((u, v))
        return pairs

    def get_even_step_pairs(n):
        """Return pairs (2u, 4u) for u in units."""
        pairs = []
        for u in get_units(n):
            v1 = (2 * u) % n
            v2 = (4 * u) % n
            if v1 != 0 and v2 != 0 and v1 != v2:
                pairs.append((v1, v2))
        return pairs

    def get_gap_pairs(n, gaps):
        """Return pairs (u, u+g) for u in units and g in gaps."""
        pairs = []
        for u in get_units(n):
            for g in gaps:
                v = (u + g) % n
                if v != 0 and v != u:
                    pairs.append((u, v))
        return pairs

    # -----------------------------------------------------------------------
    # Strategy 1: The x/y-swap Pattern
    # A = x^a + y^b + y^c,  B = y^d + x^e + x^f
    # -----------------------------------------------------------------------
    # We focus on doubling, even-steps, and specific known-good gaps (5, 7).
    
    # Precompute candidate pairs for y and x
    y_doubling = get_doubling_pairs(m)
    y_gaps = get_gap_pairs(m, [3, 5, 7]) # 5 and 7 are empirically strong
    y_all = sorted(list(set(y_doubling + y_gaps)))

    x_doubling = get_doubling_pairs(ell)
    x_near = [] 
    # Add near-doubling for x (2u +/- 1)
    for u in get_units(ell):
        for d in [-1, 1]:
            v = (2*u + d) % ell
            if v != 0 and v != u: x_near.append((u, v))
    x_all = sorted(list(set(x_doubling + x_near)))

    # Pivots
    a_pivots = [x for x in [1, 2, 3, ell//2] if 0 < x < ell]
    d_pivots = [x for x in [1, 2, 3, m//2] if 0 < x < m]

    # Combine
    # Limit loops to avoid timeout/memory issues
    for a in a_pivots:
        for b_pair in y_all:
            A = [(a, 0), (0, b_pair[0]), (0, b_pair[1])]
            
            for d in d_pivots:
                # Prioritize pure doubling for B first
                for e_pair in x_doubling:
                    B = [(0, d), (e_pair[0], 0), (e_pair[1], 0)]
                    _add(A, B)
                    if len(candidates) > 3000: break
                
                if len(candidates) > 3000: break
                
                # If we have room, try near-doubling/mixed
                if len(candidates) < 2000:
                    for e_pair in x_near:
                        B = [(0, d), (e_pair[0], 0), (e_pair[1], 0)]
                        _add(A, B)
                        if len(candidates) > 3000: break
            if len(candidates) > 3000: break
        if len(candidates) > 3000: break

    # -----------------------------------------------------------------------
    # Strategy 2: Constant-Monomial Families (Linked)
    # A = 1 + y^u + y^v, B = 1 + x^p + x^q
    # -----------------------------------------------------------------------
    # We construct "families" of polynomials: Doubling, Even-Step.
    
    # 1. Generate interesting A polynomials
    A_polys = []
    # Doubling
    for p in get_doubling_pairs(m):
        A_polys.append([(0,0), (0,p[0]), (0,p[1])])
    # Even-step (1 + y^2u + y^4u)
    for p in get_even_step_pairs(m):
        A_polys.append([(0,0), (0,p[0]), (0,p[1])])
        
    # 2. Generate interesting B polynomials
    B_polys = []
    for p in get_doubling_pairs(ell):
        B_polys.append([(0,0), (p[0],0), (p[1],0)])
    for p in get_even_step_pairs(ell):
        B_polys.append([(0,0), (p[0],0), (p[1],0)])

    # 3. Combine them
    for A in A_polys:
        for B in B_polys:
            _add(A, B)

    # -----------------------------------------------------------------------
    # Strategy 3: Linked Scaling (Structure Mapping)
    # If A = 1 + y^u + y^v, try B = 1 + x^su + x^sv
    # -----------------------------------------------------------------------
    scales = [1, 2, 3, 5, 7]
    for A in A_polys:
        # Extract exponents u, v
        exps = [t[1] for t in A if t[1] != 0]
        if len(exps) != 2: continue
        u, v = exps
        
        for s in scales:
            u_x = (u * s) % ell
            v_x = (v * s) % ell
            if u_x == 0 or v_x == 0 or u_x == v_x: continue
            
            B = [(0,0), (u_x, 0), (v_x, 0)]
            _add(A, B)

    # -----------------------------------------------------------------------
    # Strategy 4: Perturbations of Known Codes
    # -----------------------------------------------------------------------
    for code_spec in KNOWN_CODES:
        if code_spec["ell"] == ell and code_spec["m"] == m:
            base_A = code_spec["A_terms"]
            base_B = code_spec["B_terms"]
            _add(base_A, base_B)

            # Perturb non-zero exponents
            for delta in [-1, 1]:
                for i in range(3):
                    # Perturb A
                    new_A = list(base_A)
                    x, y = new_A[i]
                    if x > 0: new_A[i] = ((x + delta) % ell, y)
                    elif y > 0: new_A[i] = (x, (y + delta) % m)
                    _add(new_A, base_B)

                    # Perturb B
                    new_B = list(base_B)
                    x, y = new_B[i]
                    if x > 0: new_B[i] = ((x + delta) % ell, y)
                    elif y > 0: new_B[i] = (x, (y + delta) % m)
                    _add(base_A, new_B)

    return candidates
# EVOLVE-BLOCK-END
