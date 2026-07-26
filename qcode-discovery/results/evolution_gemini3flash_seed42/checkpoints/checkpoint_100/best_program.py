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
    """Generate candidate (A_terms, B_terms) pairs for given lattice dimensions.

    This is the function that gets evolved by the LLM. The initial version
    uses algebraic heuristics based on known good code patterns.

    Args:
        ell: Cyclic group order for x.
        m: Cyclic group order for y.

    Returns:
        List of (A_terms, B_terms) pairs to evaluate.
    """
    candidates = []
    seen = set()

    def _add(a_terms, b_terms):
        """Add candidate if not a duplicate."""
        key = (tuple(sorted(a_terms)), tuple(sorted(b_terms)))
        if key not in seen:
            seen.add(key)
            candidates.append((list(a_terms), list(b_terms)))

    # Strategy 1: Pure-Axis / Decoupled Patterns (Matches [[360,40,24]] and [[144,32,14]])
    # Often yields the highest k (logical qubits).
    y_pats = [(1, 2), (2, 4), (3, 6), (1, 3), (2, 7), (m//3, 2*m//3)]
    x_pats = [(1, 2), (2, 4), (3, 4), (3, 6), (4, 8), (2, 5), (ell//3, 2*ell//3)]
    for y1, y2 in y_pats:
        if 0 < y1 < y2 < m:
            A_pure = [(0, 0), (0, y1), (0, y2)]
            for x1, x2 in x_pats:
                if 0 < x1 < x2 < ell:
                    B_pure = [(0, 0), (x1, 0), (x2, 0)]
                    _add(A_pure, B_pure)
                    _add(B_pure, A_pure)

    # Strategy 2: Focused x/y-swap (A=x^a + y^b + y^c, B=y^d + x^e + x^f)
    # Using small prime offsets and doubling patterns.
    for a in [1, 3, 5, ell//2]:
        if not (0 < a < ell): continue
        for b in [1, 2, 3]:
            if b >= m: continue
            for c in [(2*b)%m, (m-b)%m, (b+3)%m]:
                if c == b or c == 0 or c >= m: continue
                A = [(a, 0), (0, b), (0, c)]
                for d in [1, 3, 5, m//2]:
                    if not (0 < d < m): continue
                    for e in [1, 2, 3]:
                        if e >= ell: continue
                        for f in [(2*e)%ell, (ell-e)%ell, (e+3)%ell]:
                            if f == e or f == 0 or f >= ell: continue
                            _add(A, [(0, d), (e, 0), (f, 0)])

    # Strategy 3: Perturbations of known good codes at this lattice
    for code_spec in KNOWN_CODES:
        if code_spec["ell"] == ell and code_spec["m"] == m:
            base_A = code_spec["A_terms"]
            base_B = code_spec["B_terms"]
            _add(base_A, base_B)

            # Perturb each exponent by ±1, ±2
            for delta in [-2, -1, 1, 2]:
                for i in range(3):
                    for coord in [0, 1]:  # x or y exponent
                        new_A = [list(t) for t in base_A]
                        limit = ell if coord == 0 else m
                        new_A[i][coord] = (new_A[i][coord] + delta) % limit
                        new_A_tuples = [tuple(t) for t in new_A]
                        if len(set(new_A_tuples)) == 3:
                            _add(new_A_tuples, base_B)

                        new_B = [list(t) for t in base_B]
                        limit = ell if coord == 0 else m
                        new_B[i][coord] = (new_B[i][coord] + delta) % limit
                        new_B_tuples = [tuple(t) for t in new_B]
                        if len(set(new_B_tuples)) == 3:
                            _add(base_A, new_B_tuples)

    # Strategy 4: Canonical Scaling and Targeted x/y-swap
    # Includes the "gross code" and known high-performance generators.
    canonical_polys = [
        ([(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)]),
        ([(9, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)]),
        ([(3, 0), (0, 2), (0, 7)], [(0, 3), (1, 0), (2, 0)]), # [[288,12,18]]
        ([(0, 0), (5, 0), (10, 0)], [(0, 0), (0, 1), (0, 2)]), # [[360,40,24]] pattern
    ]
    for A, B in canonical_polys:
        if all(x < ell and y < m for x, y in A) and all(x < ell and y < m for x, y in B):
            _add(A, B)

    # Strategy 5: Harmonic and Symmetric Patterns
    # Includes the 1:2:4 ratio and the [[144,32,12]] symmetric structure.
    import math
    def get_interesting_exponents(limit):
        # Focus on small integers, midpoints, and primes
        steps = [0, 1, 2, 3, 4, 5, 6, 7, limit // 2, limit // 3]
        return sorted(list(set([s % limit for s in steps if s < limit])))

    x_ints = get_interesting_exponents(ell)
    y_ints = get_interesting_exponents(m)

    for a in x_ints:
        for b in y_ints:
            for c in y_ints:
                if b >= c: continue
                A = [(a, 0), (0, b), (0, c)]
                # Sub-strategy: Symmetric B (Matches [[144,32,12]])
                # Normalized form of A=[(4,0),(0,2),(0,0)] B=[(0,2),(4,0),(0,0)]
                B_sym = [(0, a % m if a < m else 1), (b % ell if b < ell else 1, 0), (c % ell if c < ell else 0, 0)]
                if len(set(B_sym)) == 3:
                    _add(A, B_sym)
                
                # Sub-strategy: Harmonic/Swap B
                # Test different multipliers (2, 3) and offsets to find higher k
                for d in y_ints:
                    for e in x_ints:
                        if e == 0: continue
                        for mult in [2, 3]:
                            f = (mult * e) % ell
                            if f == e or f == 0: continue
                            B = [(0, d), (e, 0), (f, 0)]
                            if len(set(B)) == 3:
                                _add(A, B)
                        # Try a "shifted" swap for k-diversity
                        B_shift = [(0, d), (e, 0), ((e + ell//2) % ell, 0)]
                        if len(set(B_shift)) == 3:
                            _add(A, B_shift)

    # Strategy 6: Gapped and Coprime Patterns (Pruned for n > 5000 safety)
    import math
    cop_x = [i for i in [1, 3, 7] if i < ell and math.gcd(i, ell) == 1]
    cop_y = [i for i in [1, 3, 7] if i < m and math.gcd(i, m) == 1]
    
    for ax in cop_x:
        for by in [1, 2]:
            if by >= m: continue
            for gap in [3, 5, 7]:
                cy = (by + gap) % m
                if cy == by or cy == 0 or cy >= m: continue
                A = [(ax, 0), (0, by), (0, cy)]
                for dy in cop_y:
                    for ex in [1, 2]:
                        if ex >= ell: continue
                        fx = (ex + gap) % ell
                        if fx == ex or fx == 0 or fx >= ell: continue
                        _add(A, [(0, dy), (ex, 0), (fx, 0)])

    # Strategy 6: Asymmetric Mix (Breaks k=2 trapping)
    # A = x^a + y^b + x^c, B = y^d + x^e + y^f
    for a in [1, 2, 3]:
        for b in [1, 2]:
            for c in [ell // 2, ell // 3]:
                if c == 0 or c == a: continue
                A = [(a, 0), (0, b), (c, 0)]
                for d in [1, 2, 3]:
                    for e in [1, 2]:
                        for f in [m // 2, m // 3]:
                            if f == 0 or f == d: continue
                            B = [(0, d), (e, 0), (0, f)]
                            if len(set(A)) == 3 and len(set(B)) == 3:
                                _add(A, B)

    return candidates
# EVOLVE-BLOCK-END
