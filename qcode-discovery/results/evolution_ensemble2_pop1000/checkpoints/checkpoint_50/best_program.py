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

    def _add(a_terms, b_terms):
        """Add candidate if not a duplicate."""
        key = (tuple(sorted(a_terms)), tuple(sorted(b_terms)))
        if key not in seen:
            seen.add(key)
            candidates.append((list(a_terms), list(b_terms)))

    def _gcd(a, b):
        while b:
            a, b = b, a % b
        return a

    def _coprime(a, n):
        return _gcd(a, n) == 1

    # -----------------------------------------------------------------------
    # Strategy 1: Linked Polynomials (Generalized "Gross" & "High-k" logic)
    # The best codes often satisfy B(x) ~ A(y^k) or similar structural links.
    # We define a set of "seed" polynomials P(z) = 1 + z^a + z^b.
    # Then we set A = P(y) (possibly scaled) and B = P(x^k) (scaled).
    # -----------------------------------------------------------------------
    
    # Seed exponents (a, b) for polynomial 1 + z^a + z^b
    # We include doubling (1,2), tripling (1,3), and some gaps.
    seeds = [
        (1, 2), # 1+z+z^2 (classic)
        (1, 3), # 1+z+z^3
        (2, 3), 
        (1, 4),
        (2, 4), # (1+z+z^2)^2
        (3, 4),
        (1, 5),
        (2, 5),
        (3, 5),
        (2, 7), # From [[90,8,10]]
    ]
    
    # Expand seeds with some larger strides if lattice is large
    if m > 12:
        seeds.append((3, 6))
        seeds.append((4, 8))

    for (sa, sb) in seeds:
        # Create A candidates based on seed P(y)
        # We try A = 1 + y^sa + y^sb
        # And also scaled versions A = 1 + y^(k*sa) + y^(k*sb)
        
        # Limit scaling to keep candidate count reasonable
        # We want scalings that might be coprime to m, or factors of m.
        a_scalings = [1]
        if m % 2 == 0: a_scalings.append(m//2 - 1)
        for k in range(2, 5):
            if _coprime(k, m): a_scalings.append(k)

        for ka in a_scalings:
            exp_a1 = (ka * sa) % m
            exp_a2 = (ka * sb) % m
            if exp_a1 == 0 or exp_a2 == 0 or exp_a1 == exp_a2: continue
            
            # Sub-strategy 1.1: Pure Y in A, Pure X in B (Constant Monomials)
            # This targets codes like [[360,40]] where A=1+y+y^2, B=1+x^5+x^10
            A_pure = [(0,0), (0, exp_a1), (0, exp_a2)]
            
            # Try matching B on x-side using same seed structure, scaled
            for kb in range(1, ell):
                # Heuristic: kb often related to divisors or coprime
                if not (ell % kb == 0 or _coprime(kb, ell) or kb < 6): continue
                
                exp_b1 = (kb * sa) % ell
                exp_b2 = (kb * sb) % ell
                if exp_b1 == 0 or exp_b2 == 0 or exp_b1 == exp_b2: continue
                
                B_pure = [(0,0), (exp_b1, 0), (exp_b2, 0)]
                _add(A_pure, B_pure)

            # Sub-strategy 1.2: Mixed x/y-swap with Seed Structure
            # A = x^u + y^exp_a1 + y^exp_a2
            # B = y^v + x^exp_b1 + x^exp_b2
            # We pick u, v from small numbers or factors (like ell/2)
            u_vals = [ell//2, ell//3, 3, 1] if ell > 4 else [1]
            v_vals = [m//2, m//3, 3, 1] if m > 4 else [1]
            
            # Filter valid u, v
            u_vals = [u for u in u_vals if 0 < u < ell]
            v_vals = [v for v in v_vals if 0 < v < m]
            
            # Reuse a small set of B scalings for the mixed case
            b_scalings_mixed = [1, 2, 3]
            
            for u in u_vals:
                A_mixed = [(u, 0), (0, exp_a1), (0, exp_a2)]
                
                for v in v_vals:
                    for kb in b_scalings_mixed:
                        exp_b1 = (kb * sa) % ell
                        exp_b2 = (kb * sb) % ell
                        if exp_b1 == 0 or exp_b2 == 0 or exp_b1 == exp_b2: continue
                        if exp_b1 == u or exp_b2 == u: continue
                        
                        B_mixed = [(0, v), (exp_b1, 0), (exp_b2, 0)]
                        _add(A_mixed, B_mixed)

    # -----------------------------------------------------------------------
    # Strategy 2: Explicit Coprime/Gap Search
    # This finds the "weird" codes that don't fit the seed patterns.
    # -----------------------------------------------------------------------
    max_a = min(ell, 8) 
    max_y = min(m, 8)
    
    # Iterate x-exponent for A (a) and y-exponent for B (d)
    # We restrict these to be small or coprime
    search_a = [x for x in range(1, max_a) if _coprime(x, ell)]
    search_d = [y for y in range(1, max_y) if _coprime(y, m)]
    
    # Iterate base y-exponent for A (b) and x-exponent for B (e)
    # These drive the "doubling" or "gap" logic
    search_b = [y for y in range(1, m//2 + 2) if _coprime(y, m)]
    search_e = [x for x in range(1, ell//2 + 2) if _coprime(x, ell)]
    
    # Gaps to try: c = b + gap
    gaps = [1, 2, 3, 5, 7]

    for a in search_a:
        for b in search_b:
            # Generate A candidates
            A_list = []
            
            # Doubling
            c = (2*b) % m
            if c != b and c != 0:
                A_list.append([(a,0), (0,b), (0,c)])
            
            # Gaps
            for g in gaps:
                c = (b + g) % m
                if c != b and c != 0:
                     A_list.append([(a,0), (0,b), (0,c)])
            
            if not A_list: continue
            
            for d in search_d:
                for e in search_e:
                    # Generate B candidates (Doubling & Gaps)
                    
                    # Doubling B
                    f = (2*e) % ell
                    if f != e and f != 0:
                        B = [(0,d), (e,0), (f,0)]
                        for A in A_list: _add(A, B)
                    
                    # Gap B (only 1 and 5 to save time)
                    for g in [1, 5]:
                        f = (e + g) % ell
                        if f != e and f != 0:
                            B = [(0,d), (e,0), (f,0)]
                            for A in A_list: _add(A, B)

    # -----------------------------------------------------------------------
    # Strategy 3: Perturbations of Known Good Codes
    # -----------------------------------------------------------------------
    for code_spec in KNOWN_CODES:
        if code_spec["ell"] == ell and code_spec["m"] == m:
            base_A = code_spec["A_terms"]
            base_B = code_spec["B_terms"]
            _add(base_A, base_B)

            # Perturb by ±1
            for delta in [-1, 1]:
                # Perturb A
                for i in range(len(base_A)):
                    if base_A[i] == (0,0): continue
                    new_A = list(base_A)
                    x, y = new_A[i]
                    if x > 0: x = (x + delta) % ell
                    if y > 0: y = (y + delta) % m
                    new_A[i] = (x, y)
                    if len(set(new_A)) == 3:
                        _add(new_A, base_B)

                # Perturb B
                for i in range(len(base_B)):
                    if base_B[i] == (0,0): continue
                    new_B = list(base_B)
                    x, y = new_B[i]
                    if x > 0: x = (x + delta) % ell
                    if y > 0: y = (y + delta) % m
                    new_B[i] = (x, y)
                    if len(set(new_B)) == 3:
                        _add(base_A, new_B)

    return candidates
# EVOLVE-BLOCK-END
