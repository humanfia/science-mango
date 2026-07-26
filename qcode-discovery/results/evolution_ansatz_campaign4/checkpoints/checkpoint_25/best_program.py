"""Seed solution for the novel-ansatz discovery campaign (Campaign 6).

This seed provides diverse starting strategies to discover NOVEL structural
families of BB codes beyond the 3 known families (x/y-swap, constant-monomial,
Bravyi standard).  It explores mixed monomials, multi-term polynomials,
non-standard pure-term patterns, algebraic constructions, and hybrid patterns.

Top-level objects:

``KNOWN_CODES`` : list[dict]
    14 verified BB codes -- regression baselines.

``TARGET_LATTICES`` : list[tuple[int, int]]
    18 target (ell, m) lattice dimensions.

``REFERENCE_CODES`` : list[dict]
    Known pure-term codes at key lattices.  Used by ``_safety_net_codes``
    to guarantee the cascade always has k > 0 fallback codes.

``_safety_net_codes(ell, m)`` : function
    Returns known pure-term codes for the given lattice.  Defined OUTSIDE
    the EVOLVE-BLOCK so the LLM cannot remove it.

``generate_candidates(ell, m)`` : function
    The function that OpenEvolve evolves -- enclosed between
    ``# EVOLVE-BLOCK-START`` and ``# EVOLVE-BLOCK-END`` markers.
    Six strategies:

    1. **Mixed-monomial trinomials** -- diagonal shifts on the torus.
    2. **Multi-term extensions** -- add a 4th term (pure or mixed) to
       reference codes.
    3. **Non-standard pure-term patterns** -- 4-term pure polynomials not
       matching x/y-swap or constant-monomial structure.
    4. **Algebraic constructions** -- B derived from A via coordinate
       transforms or monomial multiplication.
    5. **Hybrid patterns** -- cross-family: constant-monomial A with
       x/y-swap B, and vice versa.
    6. **Perturbations of reference codes** -- exponent shifts as fallback.
"""

from __future__ import annotations

# ---------------------------------------------------------------------------
# Known BB codes -- verified against qldpc (n, k match exactly)
# ---------------------------------------------------------------------------
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


# ---------------------------------------------------------------------------
# Reference codes for the safety net (known pure-term codes at key lattices)
# ---------------------------------------------------------------------------
REFERENCE_CODES = [
    # Stage 1 lattices -- safety net must guarantee k > 0 at both
    {"ell": 6, "m": 6,
     "A": [(3, 0), (0, 1), (0, 2)],
     "B": [(0, 3), (1, 0), (2, 0)]},
    {"ell": 12, "m": 6,
     "A": [(3, 0), (0, 1), (0, 2)],
     "B": [(0, 3), (1, 0), (2, 0)]},
    # Stage 2 lattices -- also seeds for strategies 2-4
    {"ell": 6, "m": 12,
     "A": [(3, 0), (0, 1), (0, 2)],
     "B": [(0, 3), (1, 0), (2, 0)]},
    {"ell": 24, "m": 6,
     "A": [(6, 0), (0, 1), (0, 2)],
     "B": [(0, 3), (2, 0), (4, 0)]},
    {"ell": 12, "m": 12,
     "A": [(6, 0), (0, 1), (0, 2)],
     "B": [(0, 3), (2, 0), (4, 0)]},
    # Best known codes at n=360 lattices
    {"ell": 15, "m": 12,
     "A": [(0, 0), (0, 1), (0, 2)],
     "B": [(0, 0), (5, 0), (10, 0)]},
    {"ell": 30, "m": 6,
     "A": [(9, 0), (0, 1), (0, 2)],
     "B": [(0, 3), (25, 0), (26, 0)]},
]


def _safety_net_codes(ell, m):
    """Always include known pure-term codes to keep cascade alive.

    OUTSIDE EVOLVE-BLOCK -- the LLM cannot remove these.  Without them,
    if all novel codes have k=0, the cascade threshold (0.01) is never met,
    stage 2 never runs, and the LLM never gets distance feedback.
    """
    codes = []
    for ref in REFERENCE_CODES:
        if ref["ell"] == ell and ref["m"] == m:
            codes.append((list(ref["A"]), list(ref["B"])))
    return codes


# EVOLVE-BLOCK-START
def generate_candidates(
    ell: int, m: int
) -> list[tuple[list[tuple[int, int]], list[tuple[int, int]]]]:
    """Generate candidate (A_terms, B_terms) pairs for given lattice dimensions.

    This is the function that gets evolved by the LLM.  The initial version
    provides diverse strategies to discover novel structural families beyond
    x/y-swap and constant-monomial codes.

    Args:
        ell: Cyclic group order for x.
        m: Cyclic group order for y.

    Returns:
        List of (A_terms, B_terms) pairs to evaluate.
    """
    from math import gcd

    # Start with safety-net codes (defined outside this block, non-removable)
    candidates = list(_safety_net_codes(ell, m))
    seen = {(tuple(sorted(a)), tuple(sorted(b))) for a, b in candidates}

    def _add(a_terms, b_terms):
        """Add candidate if not a duplicate and not self-dual (A=B always d=2)."""
        if sorted(a_terms) == sorted(b_terms):
            return
        key = (tuple(sorted(a_terms)), tuple(sorted(b_terms)))
        if key not in seen:
            seen.add(key)
            candidates.append((list(a_terms), list(b_terms)))

    # -----------------------------------------------------------------
    # Strategy 1: Mixed-monomial trinomials
    # -----------------------------------------------------------------
    # A = 1 + x^a1*y^a2 + x^a3*y^a4
    # B = 1 + x^b1*y^b2 + x^b2*y^b1  (transpose pattern for B's third term)
    #
    # The constant term (0,0) = identity matrix anchors the construction.
    # Mixed monomials x^a*y^b create diagonal shifts coupling both cyclic
    # dimensions.  The "transpose" pattern creates complementary shifts.
    max_ex = min(ell, 5)
    max_ey = min(m, 5)

    for a1x in range(1, max_ex):
        for a1y in range(1, max_ey):
            for a2x in range(0, max_ex):
                for a2y in range(0, max_ey):
                    A = [(0, 0), (a1x, a1y), (a2x, a2y)]
                    if len(set(A)) != 3:
                        continue
                    for b1x in range(1, max_ex):
                        for b1y in range(1, max_ey):
                            b2x = b1y % ell
                            b2y = b1x % m
                            B = [(0, 0), (b1x, b1y), (b2x, b2y)]
                            if len(set(B)) == 3:
                                _add(A, B)

    # -----------------------------------------------------------------
    # Strategy 2: Multi-term extensions (4 terms, pure or mixed)
    # -----------------------------------------------------------------
    # Add a 4th term to reference codes.  Unlike the old version that only
    # added mixed monomials, this also tries pure x-terms and pure y-terms
    # to test whether term count matters independently of monomial type.
    for ref in REFERENCE_CODES:
        if ref["ell"] == ell and ref["m"] == m:
            base_A = ref["A"]
            base_B = ref["B"]
            max_e = min(max(ell, m), 8)
            # Add pure x-terms
            for ex in range(1, min(ell, max_e)):
                extra = (ex, 0)
                if extra not in base_A:
                    _add(base_A + [extra], base_B)
                if extra not in base_B:
                    _add(base_A, base_B + [extra])
            # Add pure y-terms
            for ey in range(1, min(m, max_e)):
                extra = (0, ey)
                if extra not in base_A:
                    _add(base_A + [extra], base_B)
                if extra not in base_B:
                    _add(base_A, base_B + [extra])
            # Add mixed monomials
            for ax in range(1, min(ell, 5)):
                for ay in range(1, min(m, 5)):
                    extra = (ax, ay)
                    if extra not in base_A:
                        _add(base_A + [extra], base_B)
                    if extra not in base_B:
                        _add(base_A, base_B + [extra])

    # -----------------------------------------------------------------
    # Strategy 3: Non-standard pure-term patterns
    # -----------------------------------------------------------------
    # 3- and 4-term polynomials mixing x-terms, y-terms, and constant
    # in combinations that DON'T match x/y-swap or constant-monomial.
    max_x = min(ell, 6)
    max_y = min(m, 6)

    # 3a: A = 1 + x^a + y^b (constant + x + y), B = 1 + x^c + y^d
    # Neither matches x/y-swap (which has NO constant) nor constant-monomial
    # (which is univariate: A=f(y), B=g(x)).
    for a in range(1, max_x):
        for b in range(1, max_y):
            A = [(0, 0), (a, 0), (0, b)]
            for c in range(1, max_x):
                for d in range(1, max_y):
                    B = [(0, 0), (c, 0), (0, d)]
                    if len(set(B)) == 3:
                        _add(A, B)

    # 3b: Symmetric Diagonal Shifts (Novel Ansatz)
    # A = 1 + x^a*y^a + x^b*y^b  (Main diagonal)
    # B = 1 + x^a*y^-a + x^b*y^-b (Anti-diagonal)
    for a in range(1, min(ell, m, 6)):
        for b in range(a + 1, min(ell, m, 8)):
            A = [(0, 0), (a, a), (b, b)]
            B = [(0, 0), (a, (-a) % m), (b, (-b) % m)]
            if len(set(A)) == 3 and len(set(B)) == 3:
                _add(A, B)
                # Try 4-term variant by adding another diagonal
                for c in range(b + 1, min(ell, m, 10)):
                    A4 = A + [(c, c)]
                    B4 = B + [(c, (-c) % m)]
                    if len(set(A4)) == 4 and len(set(B4)) == 4:
                        _add(A4, B4)

    # -----------------------------------------------------------------
    # Strategy 4: Algebraic constructions (B derived from A)
    # -----------------------------------------------------------------
    # B = A(x^s, y^t) — coordinate transform.  For coprime s with ell
    # and coprime t with m, this is a ring automorphism.
    base_trinomials = [
        [(3, 0), (0, 1), (0, 2)],   # gross code A
        [(0, 0), (0, 1), (0, 2)],   # constant-monomial A (1+y+y^2)
        [(0, 0), (1, 0), (0, 1)],   # 1+x+y
    ]
    for A in base_trinomials:
        for s in range(1, min(ell, 8)):
            if gcd(s, ell) != 1:
                continue
            for t in range(1, min(m, 8)):
                if gcd(t, m) != 1:
                    continue
                if s == 1 and t == 1:
                    continue  # identity transform
                B = [((a * s) % ell, (b * t) % m) for a, b in A]
                if len(set(B)) == len(B):
                    _add(A, B)

    # B = x^a * y^b * A — monomial shift of A (shared ideal structure)
    for A in base_trinomials:
        for sx in range(0, min(ell, 5)):
            for sy in range(0, min(m, 5)):
                if sx == 0 and sy == 0:
                    continue  # would give A=B
                B = [((a + sx) % ell, (b + sy) % m) for a, b in A]
                if len(set(B)) == len(B):
                    _add(A, B)

    # -----------------------------------------------------------------
    # Strategy 5: Hybrid patterns (cross-family)
    # -----------------------------------------------------------------
    # Constant-monomial A + x/y-swap B
    for a in range(1, max_y):
        for b in range(a + 1, max_y):
            A_cm = [(0, 0), (0, a), (0, b)]  # 1 + y^a + y^b
            if len(set(A_cm)) != 3:
                continue
            for d in range(1, max_y):
                for e in range(1, max_x):
                    for f in range(e + 1, max_x):
                        B_swap = [(0, d), (e, 0), (f, 0)]  # y^d + x^e + x^f
                        if len(set(B_swap)) == 3:
                            _add(A_cm, B_swap)

    # x/y-swap A + constant-monomial B
    for a in range(1, max_x):
        for b in range(1, max_y):
            for c in range(b + 1, max_y):
                A_swap = [(a, 0), (0, b), (0, c)]  # x^a + y^b + y^c
                if len(set(A_swap)) != 3:
                    continue
                for d in range(1, max_x):
                    for e in range(d + 1, max_x):
                        B_cm = [(0, 0), (d, 0), (e, 0)]  # 1 + x^d + x^e
                        if len(set(B_cm)) == 3:
                            _add(A_swap, B_cm)

    # Asymmetric term count: 3-term A + 4-term B
    for ref in REFERENCE_CODES:
        if ref["ell"] == ell and ref["m"] == m:
            A3 = ref["A"]
            B3 = ref["B"]
            # Add constant to B (if not already there)
            if (0, 0) not in B3:
                _add(A3, B3 + [(0, 0)])
            # Add constant to A
            if (0, 0) not in A3:
                _add(A3 + [(0, 0)], B3)

    # -----------------------------------------------------------------
    # Strategy 6: Perturbations of reference codes
    # -----------------------------------------------------------------
    # Standard +/-1, +/-2 shifts on each exponent of each term.
    for ref in REFERENCE_CODES:
        if ref["ell"] == ell and ref["m"] == m:
            base_A = ref["A"]
            base_B = ref["B"]
            _add(base_A, base_B)

            for delta in [-2, -1, 1, 2]:
                for i in range(len(base_A)):
                    for coord in [0, 1]:
                        new_A = [list(t) for t in base_A]
                        limit = ell if coord == 0 else m
                        new_A[i][coord] = (new_A[i][coord] + delta) % limit
                        new_A_tuples = [tuple(t) for t in new_A]
                        if len(set(new_A_tuples)) == len(new_A_tuples):
                            _add(new_A_tuples, base_B)

                        new_B = [list(t) for t in base_B]
                        limit = ell if coord == 0 else m
                        new_B[i][coord] = (new_B[i][coord] + delta) % limit
                        new_B_tuples = [tuple(t) for t in new_B]
                        if len(set(new_B_tuples)) == len(new_B_tuples):
                            _add(base_A, new_B_tuples)

    return candidates
# EVOLVE-BLOCK-END
