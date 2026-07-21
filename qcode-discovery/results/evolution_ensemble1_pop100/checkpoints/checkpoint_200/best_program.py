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
    """Generate candidate (A_terms, B_terms) pairs for given lattice dimensions.

    Focus: generate fewer but *higher-quality* BB candidates by:
      - emphasizing constant-monomial (A(y), B(x)) families that boost k,
      - adding structured "linked kernel" transforms (B = A(x^c) and variants),
      - adding sparse nonconsecutive exponent patterns (known to help distance),
      - enforcing lightweight coprimality / degeneracy filters early.

    Args:
        ell: Cyclic group order for x.
        m: Cyclic group order for y.

    Returns:
        List of (A_terms, B_terms) pairs to evaluate.
    """
    import math

    candidates: list[tuple[list[tuple[int, int]], list[tuple[int, int]]]] = []
    seen: set[tuple[tuple[tuple[int, int], ...], tuple[tuple[int, int], ...]]] = set()

    def _norm(terms: list[tuple[int, int]]) -> tuple[tuple[int, int], ...]:
        # canonical ordering + remove duplicates (GF(2) duplicates would cancel anyway)
        return tuple(sorted(set((a % ell, b % m) for a, b in terms)))

    def _add(a_terms, b_terms):
        a_key = _norm(list(a_terms))
        b_key = _norm(list(b_terms))
        if len(a_key) < 2 or len(b_key) < 2:
            return
        key = (a_key, b_key)
        if key not in seen:
            seen.add(key)
            candidates.append((list(a_key), list(b_key)))

    def _gcd(a: int, n: int) -> int:
        return math.gcd(a % n, n)

    def _units_mod(n: int, max_count: int = 12) -> list[int]:
        # small set of "good" steps: units and near-units
        base = []
        for t in range(1, n):
            if _gcd(t, n) == 1:
                base.append(t)
        # prefer small + also include n-1 symmetry
        base = sorted(base, key=lambda x: min(x, n - x))
        # keep a compact representative set
        out = []
        for x in base:
            if x not in out:
                out.append(x)
            if len(out) >= max_count:
                break
        return out

    # -----------------------------------------------------------------------
    # Strategy 0: Always include exact known codes for this lattice
    # (keeps strong anchors; also helps when same pair works on multiple lattices)
    # -----------------------------------------------------------------------
    for code_spec in KNOWN_CODES:
        if code_spec["ell"] == ell and code_spec["m"] == m:
            _add(code_spec["A_terms"], code_spec["B_terms"])

    # -----------------------------------------------------------------------
    # Strategy 1: Constant-monomial high-k families with strong structure
    # A = 1 + y^a + y^b,  B = 1 + x^c + x^d
    # Emphasize:
    #   - (1, t, 2t) "doubling" (linked-kernel-like),
    #   - sparse nonconsecutive (t, 3t), (t, 5t),
    #   - a few small "irreducible-ish" triples such as (1,2), (1,3), (2,5)
    # and require gcd(step, size)=1 to avoid short cycles.
    # -----------------------------------------------------------------------
    y_steps = _units_mod(m, max_count=10)
    x_steps = _units_mod(ell, max_count=10)

    # "templates" expressed as multipliers of a step t
    y_templates = [(1, 2), (1, 3), (1, 5), (2, 5), (1, 7)]
    x_templates = [(1, 2), (1, 3), (1, 5), (2, 5), (1, 7)]

    for ty in y_steps:
        for u, v in y_templates:
            a = (u * ty) % m
            b = (v * ty) % m
            if a == 0 or b == 0 or a == b:
                continue
            Ay = [(0, 0), (0, a), (0, b)]
            for tx in x_steps:
                for p, q in x_templates:
                    c = (p * tx) % ell
                    d = (q * tx) % ell
                    if c == 0 or d == 0 or c == d:
                        continue
                    Bx = [(0, 0), (c, 0), (d, 0)]
                    _add(Ay, Bx)

    # Small dense neighborhood - only for small exponents to avoid explosion
    for a in range(1, min(m, 6)):
        for b in range(a + 1, min(m, 7)):
            Ay = [(0, 0), (0, a), (0, b)]
            for c in range(1, min(ell, 6)):
                for d in range(c + 1, min(ell, 7)):
                    Bx = [(0, 0), (c, 0), (d, 0)]
                    _add(Ay, Bx)

    # -----------------------------------------------------------------------
    # Strategy 2: Linked-kernel transforms: B = A(x^r)
    # For each A(y) = 1 + y^u + y^v from Strategy 1, try B(x) = 1 + x^(su) + x^(sv)
    # This captures the [[360,40,20]] structure where B exponents are scaled A exponents.
    # -----------------------------------------------------------------------
    scales = [1, 2, 3, 5, 7, 10, 11]
    # Collect all A_y polynomials we already generated (constant-monomial type)
    cm_A_set = set()
    for ty in y_steps:
        for u, v in y_templates:
            a = (u * ty) % m
            b = (v * ty) % m
            if a == 0 or b == 0 or a == b:
                continue
            cm_A_set.add((min(a,b), max(a,b)))
    # Add key anchors
    for a, b in [(1,2), (2,4), (1,3), (2,7), (1,5), (3,5)]:
        if a < m and b < m and a != b:
            cm_A_set.add((a, b))

    for (ya, yb) in cm_A_set:
        Ay = [(0, 0), (0, ya), (0, yb)]
        for s in scales:
            xa = (ya * s) % ell
            xb = (yb * s) % ell
            if xa == 0 or xb == 0 or xa == xb:
                continue
            Bx = [(0, 0), (xa, 0), (xb, 0)]
            _add(Ay, Bx)
        # Also try B with independent doubling structure
        for tx in x_steps:
            for p, q in [(1, 2), (1, 3), (2, 5)]:
                c = (p * tx) % ell
                d = (q * tx) % ell
                if c == 0 or d == 0 or c == d:
                    continue
                _add(Ay, [(0, 0), (c, 0), (d, 0)])

    # -----------------------------------------------------------------------
    # Strategy 3: x/y-swap with *nonconsecutive* y-exponents and doubling on x
    # A = x^a + y^b + y^c,  B = y^d + x^e + x^(2e)
    # Keep it compact by sampling b,c from a curated set of sparse pairs.
    # -----------------------------------------------------------------------
    sparse_y_pairs = []
    for t in y_steps:
        for u, v in [(1, 2), (1, 5), (2, 7), (3, 8), (1, 7)]:
            b = (u * t) % m
            c = (v * t) % m
            if b != 0 and c != 0 and b != c:
                sparse_y_pairs.append((b, c))
    # de-dup and cap
    sparse_y_pairs = list(dict.fromkeys(sparse_y_pairs))[:20]

    a_list = sorted(set([1, 2, 3, 5, 6, 9, ell // 2, ell // 3, ell // 4]))
    a_list = [a for a in a_list if 0 < a < ell][:6]

    e_list = _units_mod(ell, max_count=8)
    d_list = _units_mod(m, max_count=6)

    for a in a_list:
        for b, c in sparse_y_pairs:
            A = [(a, 0), (0, b), (0, c)]
            for d in d_list:
                for e in e_list:
                    f = (2 * e) % ell
                    if f == 0 or f == e:
                        continue
                    B = [(0, d), (e, 0), (f, 0)]
                    _add(A, B)

    # -----------------------------------------------------------------------
    # Strategy 4: Small perturbations of known-good codes for this lattice
    # Expand delta set slightly to escape local basins while staying compact.
    # -----------------------------------------------------------------------
    for code_spec in KNOWN_CODES:
        if code_spec["ell"] == ell and code_spec["m"] == m:
            base_A = list(code_spec["A_terms"])
            base_B = list(code_spec["B_terms"])
            for delta in [-1, 1]:
                for i in range(min(3, len(base_A))):
                    # perturb A
                    new_A = list(base_A)
                    x, y = new_A[i]
                    if x != 0:
                        new_A[i] = ((x + delta) % ell, y)
                        _add(new_A, base_B)
                    if y != 0:
                        new_A[i] = (x, (y + delta) % m)
                        _add(new_A, base_B)
                for i in range(min(3, len(base_B))):
                    # perturb B
                    new_B = list(base_B)
                    x, y = new_B[i]
                    if x != 0:
                        new_B[i] = ((x + delta) % ell, y)
                        _add(base_A, new_B)
                    if y != 0:
                        new_B[i] = (x, (y + delta) % m)
                        _add(base_A, new_B)

    return candidates
# EVOLVE-BLOCK-END
