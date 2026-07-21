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

    def _canon3(terms: list[tuple[int, int]]) -> list[tuple[int, int]]:
        """Normalize 3-term polynomials to handle translation equivalence."""
        # Shift so the smallest x and y exponents become 0
        xs = [t[0] for t in terms]
        ys = [t[1] for t in terms]
        min_x = min(xs)
        min_y = min(ys)
        return sorted([((x - min_x) % ell, (y - min_y) % m) for (x, y) in terms])

    def _add(a_terms, b_terms):
        """Add candidate if not a duplicate (using canonical form)."""
        # Canonicalize to remove translation duplicates
        ca = tuple(_canon3(list(a_terms)))
        cb = tuple(_canon3(list(b_terms)))
        key = (ca, cb)
        if key not in seen:
            seen.add(key)
            candidates.append((list(ca), list(cb)))

    def _gcd(a, b):
        while b:
            a, b = b, a % b
        return a

    def _coprime(a, n):
        return _gcd(a, n) == 1
    
    def _factors(n: int) -> list[int]:
        fs = []
        for i in range(1, int(n**0.5) + 1):
            if n % i == 0:
                fs.append(i)
                if i * i != n:
                    fs.append(n // i)
        return sorted(set(fs))

    # -----------------------------------------------------------------------
    # Strategy 1: Linked Constant-Monomial Codes (Targeting High k)
    # A = 1 + y^a + y^b, B = 1 + x^c + x^d
    # -----------------------------------------------------------------------
    
    A_candidates = []
    
    # 1. Systematic Seeds
    # We construct A from base shapes scaled by strides.
    # Base shapes: (1,2) is 1+y+y^2. (1,3) is 1+y+y^3.
    # We include non-consecutive gaps to help distance.
    base_shapes = [
        (1, 2), (1, 3), (1, 4), (1, 5),
        (2, 3), (2, 4), (2, 5), (2, 7),
        (3, 4), (3, 5), (3, 7)
    ]
    
    # Strides: 1, factors of m, and small integers
    # Factors of m are crucial for creating non-trivial kernels (high k).
    strides = set(range(1, min(m, 12)))
    strides |= set(_factors(m))
    strides = sorted(strides)

    for (s1, s2) in base_shapes:
        for k in strides:
            t1 = (k * s1) % m
            t2 = (k * s2) % m
            if t1 != 0 and t2 != 0 and t1 != t2:
                 A_candidates.append([(0,0), (0,t1), (0,t2)])

    # 2. Add pure doubling/tripling families for all valid exponents
    for a in range(1, m):
        if not _coprime(a, m) and a > 6: continue
        # Doubling
        b = (2 * a) % m
        if b != 0 and b != a:
            A_candidates.append([(0,0), (0,a), (0,b)])
        # Tripling
        b = (3 * a) % m
        if b != 0 and b != a:
            A_candidates.append([(0,0), (0,a), (0,b)])

    # Deduplicate A candidates using canonical form
    unique_A = []
    seen_A = set()
    for A in A_candidates:
        # Canonicalize just for deduplication of the list
        ca = tuple(_canon3(A))
        if ca not in seen_A:
            seen_A.add(ca)
            unique_A.append(list(ca))
    
    # Sort and filter A candidates
    # Heuristic: Prefer small sum of exponents (locality) but penalize tiny spread
    def _a_score(A):
        ys = sorted([t[1] for t in A])
        # A is normalized so ys[0]=0.
        a1, a2 = ys[1], ys[2]
        spread = min((a2 - a1) % m, (a1 - a2) % m)
        return (a1 + a2) + (10 if spread < 2 else 0)

    unique_A.sort(key=_a_score)
    unique_A = unique_A[:220]  # Slightly larger pool

    # 3. Generate B candidates (Linked)
    for A in unique_A:
        exps = sorted([t[1] for t in A])
        e1, e2 = exps[1], exps[2]
        
        # Link Type A: Algebraic Scaling B(x) ~ A(x^k)
        # Try k in small range + factors of ell
        k_vals = set(range(1, min(ell, 16))) | set(_factors(ell))
        for k in sorted(k_vals):
            f1 = (k * e1) % ell
            f2 = (k * e2) % ell
            if f1 != 0 and f2 != 0 and f1 != f2:
                B = [(0,0), (f1,0), (f2,0)]
                _add(A, B)
        
        # Link Type B: Coupled Doubling
        # B = 1 + x^e + x^(2e), where e is related to A's exponents
        # This is a very strong pattern in known high-k codes.
        bases = {e1, e2, (e2 - e1) % m}
        for base in bases:
            if base == 0: continue
            # Try scaling this base
            for k in range(1, 4): 
                e = (k * base) % ell
                f = (2 * e) % ell
                if e != 0 and f != 0 and e != f:
                    _add(A, [(0,0), (e,0), (f,0)])

        # Link Type C: Independent standard forms
        # Just simple doubling/tripling for small seeds
        x_seeds = set(range(1, min(ell, 10))) | set(_factors(ell))
        for x in sorted(x_seeds):
            if x == 0: continue
            # Doubling
            y = (2 * x) % ell
            if y != 0 and y != x:
                _add(A, [(0, 0), (x, 0), (y, 0)])
            # Tripling
            y = (3 * x) % ell
            if y != 0 and y != x:
                _add(A, [(0, 0), (x, 0), (y, 0)])

    # -----------------------------------------------------------------------
    # Strategy 2: Coprime x/y-swap (Targeting Distance)
    # A = x^a + y^b + y^c, B = y^d + x^e + x^f
    # -----------------------------------------------------------------------
    
    # Heads: a and d
    a_heads = [x for x in range(1, min(ell, 8)) if _coprime(x, ell)]
    if ell % 2 == 0: a_heads.append(ell // 2 - 1)
    
    d_heads = [x for x in range(1, min(m, 8)) if _coprime(x, m)]
    if m % 2 == 0: d_heads.append(m // 2 - 1)

    # Tails: y^b+y^c
    y_tails = []
    # Doubling/Tripling
    for b in range(1, m):
        if not _coprime(b, m): continue
        for mult in [2, 3]:
            c = (mult * b) % m
            if c != 0 and c != b: y_tails.append([(0,b), (0,c)])
    # Gaps
    for b in range(1, m):
        if not (_coprime(b, m) or b < 4): continue
        for g in [1, 2, 3, 5, 7, 8, 10]:
            c = (b + g) % m
            if c != 0 and c != b: y_tails.append([(0,b), (0,c)])
            
    # Deduplicate y_tails
    y_tails = [list(x) for x in set(tuple(sorted(t)) for t in y_tails)]
    y_tails.sort(key=lambda t: t[0][1] + t[1][1])
    y_tails = y_tails[:50]

    # Tails: x^e+x^f
    x_tails = []
    # Doubling/Tripling
    for e in range(1, ell):
        if not _coprime(e, ell): continue
        for mult in [2, 3]:
            f = (mult * e) % ell
            if f != 0 and f != e: x_tails.append([(e,0), (f,0)])
    # Gaps
    for e in range(1, ell):
        if not (_coprime(e, ell) or e < 4): continue
        for g in [1, 2, 3, 5, 7, 8, 10]:
            f = (e + g) % ell
            if f != 0 and f != e: x_tails.append([(e,0), (f,0)])

    # Deduplicate x_tails
    x_tails = [list(x) for x in set(tuple(sorted(t)) for t in x_tails)]
    x_tails.sort(key=lambda t: t[0][0] + t[1][0])
    x_tails = x_tails[:50]

    # Cartesian product (filtered)
    for a in a_heads:
        for d in d_heads:
            for y_tail in y_tails:
                A = [(a,0)] + y_tail
                for x_tail in x_tails:
                    B = [(0,d)] + x_tail
                    _add(A, B)
                    if len(candidates) > 8000: break
                if len(candidates) > 8000: break
            if len(candidates) > 8000: break
        if len(candidates) > 8000: break

    # -----------------------------------------------------------------------
    # Strategy 3: Perturbations + Cross-Lattice Reuse (high value, low volume)
    # -----------------------------------------------------------------------
    def _fits_mod(terms, mod_ell, mod_m):
        for (xe, ye) in terms:
            if xe % mod_ell != xe and xe != 0:
                return False
            if ye % mod_m != ye and ye != 0:
                return False
        return True

    def _swap_xy(terms):
        # (x_exp, y_exp) -> (y_exp, x_exp)
        return [(ye, xe) for (xe, ye) in terms]

    for code_spec in KNOWN_CODES:
        base_A = code_spec["A_terms"]
        base_B = code_spec["B_terms"]

        # 3a. Exact match + local perturbations
        if code_spec["ell"] == ell and code_spec["m"] == m:
            _add(base_A, base_B)

            for delta in (-1, 1):
                for i in range(len(base_A)):
                    if base_A[i] == (0, 0):
                        continue
                    new_A = list(base_A)
                    x, y = new_A[i]
                    if x > 0:
                        x = (x + delta) % ell
                    if y > 0:
                        y = (y + delta) % m
                    new_A[i] = (x, y)
                    if len(set(new_A)) == 3:
                        _add(new_A, base_B)

                for i in range(len(base_B)):
                    if base_B[i] == (0, 0):
                        continue
                    new_B = list(base_B)
                    x, y = new_B[i]
                    if x > 0:
                        x = (x + delta) % ell
                    if y > 0:
                        y = (y + delta) % m
                    new_B[i] = (x, y)
                    if len(set(new_B)) == 3:
                        _add(base_A, new_B)

        # 3b. Cross-lattice reuse if it fits directly (no modulo wrap)
        else:
            if _fits_mod(base_A, ell, m) and _fits_mod(base_B, ell, m):
                _add(base_A, base_B)

            # Also try x/y swapped reuse when dimensions allow
            # (helps when target lattices include (ell,m) and (m,ell))
            if ell == code_spec["m"] and m == code_spec["ell"]:
                _add(_swap_xy(base_A), _swap_xy(base_B))

    return candidates
# EVOLVE-BLOCK-END
