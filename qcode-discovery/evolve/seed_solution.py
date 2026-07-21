"""Seed solution for the evolutionary search.

This is the file that OpenEvolve loads and mutates.  It contains three
top-level objects:

``KNOWN_CODES`` : list[dict]
    14 verified BB codes -- 9 from Bravyi et al. 2024 (arXiv:2308.07915)
    and 5 original discoveries verified with the 150k-trial multi-decoder
    soak test.  Each entry has ``ell, m, A_terms, B_terms, expected,
    name, source``.  These serve as regression baselines and as seeds for
    the perturbation strategy inside ``generate_candidates``.

``TARGET_LATTICES`` : list[tuple[int, int]]
    18 target ``(ell, m)`` lattice dimensions covering code sizes
    ``n = 144, 200, 288, 360``.  Each size includes several factorizations
    (e.g. ``n=144`` has ``(12,6), (6,12), (9,8), (8,9), (24,3), (36,2)``).

``generate_candidates(ell, m)`` : function
    The function that OpenEvolve evolves -- enclosed between
    ``# EVOLVE-BLOCK-START`` and ``# EVOLVE-BLOCK-END`` markers.
    The seed version uses four generation strategies:

    1. **x/y-swap symmetric** -- ``A = x^a + y^b + y^(2b)``,
       ``B = y^d + x^e + x^(2e)``.  Matches the gross code pattern.
    2. **Perturbation of known codes** -- shifts each exponent of
       benchmark codes by ±1 and ±2.
    3. **Self-similar scaling** -- applies canonical polynomial pairs at
       whatever lattice size they fit.
    4. **Full x/y-swap search** -- independent y-exponents for A and
       x-exponents for B with small bound (``min(dim, 5)``).

    All strategies share a deduplication set to avoid evaluating the
    same candidate twice.

Sources:
    - Bravyi et al. 2024 (arXiv:2308.07915, Table 3)
    - qldpc examples (bivariate_bicycle_codes.ipynb)
    - Chengyu et al. 2026 (arXiv:2601.18562)
"""

from __future__ import annotations

# ---------------------------------------------------------------------------
# Known BB codes -- verified against qldpc (n, k match exactly)
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

    # Strategy 1: x/y-swap symmetric construction
    # Pattern: A = x^a + y^b + y^(2b),  B = y^d + x^e + x^(2e)
    # Matches the gross code structure. Restrict to small exponents
    # (good codes use exponents ≤ ℓ/2). The evolutionary loop will
    # expand the search beyond this initial neighborhood.
    max_a = ell // 2 + 1
    max_y = m // 2 + 1
    for a in range(1, max_a):
        for b in range(1, max_y):
            c = (2 * b) % m
            A = [(a, 0), (0, b), (0, c)]
            if len(set(A)) != 3:
                continue
            for d in range(1, max_y):
                for e in range(1, max_a):
                    f = (2 * e) % ell
                    B = [(0, d), (e, 0), (f, 0)]
                    if len(set(B)) == 3:
                        _add(A, B)

    # Strategy 2: Perturbations of known good codes at this lattice
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

    # Strategy 3: Self-similar scaling
    # If A=x^3+y+y^2, B=y^3+x+x^2 works at (6,6) and (12,6),
    # try the same polynomials at the current lattice.
    canonical_polys = [
        ([(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)]),
        ([(9, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)]),
    ]
    for A, B in canonical_polys:
        # Check exponents are in range
        if all(a < ell and b < m for a, b in A) and \
           all(a < ell and b < m for a, b in B):
            _add(A, B)

    # Strategy 4: Full x/y-swap search without the doubling constraint.
    # Strategy 1 uses c=2b, f=2e. Here we try all independent y-exponents
    # for A and x-exponents for B with small exponent bound.
    # Pattern: A = x^a + y^b + y^c (b ≠ c), B = y^d + x^e + x^f (e ≠ f)
    max_x = min(ell, 5)
    max_yy = min(m, 5)
    for a in range(1, max_x):
        for b in range(0, max_yy):
            for c in range(b + 1, max_yy):
                A = [(a, 0), (0, b), (0, c)]
                if len(set(A)) != 3:
                    continue
                for d in range(1, max_yy):
                    for e in range(0, max_x):
                        for f in range(e + 1, max_x):
                            B = [(0, d), (e, 0), (f, 0)]
                            if len(set(B)) == 3:
                                _add(A, B)

    return candidates
# EVOLVE-BLOCK-END
