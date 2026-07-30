"""Seed solution for the novel-ansatz discovery campaign (Campaign 4).

This seed provides diverse starting strategies to discover NOVEL structural
families of BB codes beyond the 3 known families (x/y-swap, constant-monomial,
Bravyi standard).  It explores mixed monomials, multi-term polynomials,
non-standard pure-term patterns, algebraic constructions, and hybrid patterns.
Every generated candidate obeys the challenge's hard CSS weight/degree budget
``|A| + |B| <= 6``.

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
    2. **Admissible asymmetric extensions** -- pair a 4-term polynomial
       with a 2-term core.
    3. **Low-support and non-standard patterns** -- exercise the 2+2,
       2+3, 3+2, and 3+3 splits.
    4. **Algebraic constructions** -- B derived from A via coordinate
       transforms or monomial multiplication.
    5. **Hybrid patterns** -- cross-family: constant-monomial A with
       x/y-swap B, and vice versa.
    6. **Perturbations of reference codes** -- exponent shifts as fallback.
"""

from __future__ import annotations


# Each BB CSS check row and qubit degree has weight |A| + |B|.  The challenge
# requires both to be at most 6, while bb_code.validate_terms requires at least
# two terms per polynomial.  These are therefore the complete admissible splits.
CHALLENGE_TERM_SPLITS = frozenset({
    (2, 2),
    (2, 3),
    (3, 2),
    (2, 4),
    (4, 2),
    (3, 3),
})


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
    from itertools import combinations
    from math import gcd

    # Build family buckets first, then round-robin them into the returned pool.
    # This prevents a combinatorially large 3+3 loop from consuming the whole
    # budget before other admissible support splits are represented.
    bucket_pool_limit = 240
    per_split_limit = 200
    per_family_limit = 120
    max_candidates = 1200
    buckets = {}
    seen = set()

    def _add(a_terms, b_terms, family):
        """Add a unique candidate only if it obeys every generation hard gate."""
        A = [tuple(term) for term in a_terms]
        B = [tuple(term) for term in b_terms]
        split = (len(A), len(B))

        # Non-negotiable challenge gate: larger supports are guaranteed to fail
        # the final CSS check-weight/qubit-degree requirement.
        if split not in CHALLENGE_TERM_SPLITS or len(A) + len(B) > 6:
            return False
        if len(set(A)) != len(A) or len(set(B)) != len(B):
            return False
        if any(not (0 <= x < ell and 0 <= y < m) for x, y in A + B):
            return False
        if sorted(A) == sorted(B):  # self-dual codes always have d=2
            return False

        key = (tuple(sorted(A)), tuple(sorted(B)))
        bucket_key = (split, str(family))
        bucket = buckets.setdefault(bucket_key, [])
        if key in seen or len(bucket) >= bucket_pool_limit:
            return False
        seen.add(key)
        bucket.append((A, B))
        return True

    # Safety-net candidates still pass through _add, so the returned list cannot
    # violate the support budget even if the reference table changes later.
    for A, B in _safety_net_codes(ell, m):
        _add(A, B, "00_safety_net")

    max_x = min(ell, 6)
    max_y = min(m, 6)
    pure_x = [(x, 0) for x in range(1, max_x)]
    pure_y = [(0, y) for y in range(1, max_y)]
    mixed = [
        (x, y)
        for x in range(1, max_x)
        for y in range(1, max_y)
    ]
    shifts = pure_x + pure_y + mixed

    # -----------------------------------------------------------------
    # Strategy 1: balanced mixed-monomial trinomials (3+3)
    # -----------------------------------------------------------------
    # Constant anchors plus complementary diagonal shifts.
    for first in mixed[:16]:
        for second in shifts[:20]:
            A = [(0, 0), first, second]
            for diagonal in mixed[:16]:
                transposed = (diagonal[1] % ell, diagonal[0] % m)
                B = [(0, 0), diagonal, transposed]
                _add(A, B, "mixed_complementary_3_3")

    # -----------------------------------------------------------------
    # Strategy 2: admissible asymmetric extensions (2+4 and 4+2)
    # -----------------------------------------------------------------
    # Extending one reference trinomial to four terms is challenge-eligible
    # only after reducing its partner to a two-term structural core.
    extras = [(0, 0)] + pure_x + pure_y + mixed
    for ref in REFERENCE_CODES:
        if ref["ell"] != ell or ref["m"] != m:
            continue
        base_A = [tuple(term) for term in ref["A"]]
        base_B = [tuple(term) for term in ref["B"]]
        for extra in extras:
            if extra not in base_B:
                B4 = base_B + [extra]
                for A2 in combinations(base_A, 2):
                    _add(A2, B4, "reference_extension_2_4")
                    _add(B4, A2, "reference_extension_4_2")
            if extra not in base_A:
                A4 = base_A + [extra]
                for B2 in combinations(base_B, 2):
                    _add(B2, A4, "reference_extension_2_4")
                    _add(A4, B2, "reference_extension_4_2")

    # General mixed 2+4 templates keep these splits alive on lattices without
    # a reference code.  Both A/B orientations are generated explicitly.
    for core_shift in shifts[:16]:
        core = [(0, 0), core_shift]
        for x_shift in pure_x[:5]:
            for y_shift in pure_y[:5]:
                diagonal = (
                    (core_shift[0] + x_shift[0]) % ell,
                    (core_shift[1] + y_shift[1]) % m,
                )
                extension = [(0, 0), x_shift, y_shift, diagonal]
                _add(core, extension, "mixed_core_2_4")
                _add(extension, core, "mixed_core_4_2")

    # -----------------------------------------------------------------
    # Strategy 3: low-support and non-standard families
    # -----------------------------------------------------------------
    # Exercise 2+2, 2+3, and 3+2 directly instead of treating 3+3 as the
    # only useful low-weight representation.
    for left_shift in shifts[:20]:
        A2 = [(0, 0), left_shift]
        for right_shift in shifts[:20]:
            B2 = [(0, 0), right_shift]
            _add(A2, B2, "binomial_2_2")

    for core_shift in shifts[:16]:
        core = [(0, 0), core_shift]
        for first, second in combinations(shifts[:18], 2):
            trinomial = [(0, 0), first, second]
            _add(core, trinomial, "asymmetric_2_3")
            _add(trinomial, core, "asymmetric_3_2")

    # Non-standard pure 3+3 patterns: constant + x + y on both sides.
    for a in pure_x:
        for b in pure_y:
            A = [(0, 0), a, b]
            for c in pure_x:
                for d in pure_y:
                    B = [(0, 0), c, d]
                    _add(A, B, "nonstandard_pure_3_3")

    # -----------------------------------------------------------------
    # Strategy 4: algebraic constructions (3+3)
    # -----------------------------------------------------------------
    # B = A(x^s, y^t) for torus automorphisms, or a monomial shift of A.
    base_trinomials = [
        [(3, 0), (0, 1), (0, 2)],
        [(0, 0), (0, 1), (0, 2)],
        [(0, 0), (1, 0), (0, 1)],
    ]
    for A in base_trinomials:
        for s in range(1, min(ell, 8)):
            if gcd(s, ell) != 1:
                continue
            for t in range(1, min(m, 8)):
                if gcd(t, m) != 1 or (s == 1 and t == 1):
                    continue
                B = [((a * s) % ell, (b * t) % m) for a, b in A]
                _add(A, B, "coordinate_transform_3_3")

        for sx in range(0, min(ell, 5)):
            for sy in range(0, min(m, 5)):
                if sx == 0 and sy == 0:
                    continue
                B = [((a + sx) % ell, (b + sy) % m) for a, b in A]
                _add(A, B, "monomial_shift_3_3")

    # -----------------------------------------------------------------
    # Strategy 5: hybrid cross-family patterns (3+3)
    # -----------------------------------------------------------------
    for a, b in combinations(pure_y, 2):
        A_cm = [(0, 0), a, b]
        for d in pure_y:
            for e, f in combinations(pure_x, 2):
                B_swap = [d, e, f]
                _add(A_cm, B_swap, "hybrid_3_3")

    for b, c in combinations(pure_y, 2):
        for a in pure_x:
            A_swap = [a, b, c]
            for d, e in combinations(pure_x, 2):
                B_cm = [(0, 0), d, e]
                _add(A_swap, B_cm, "hybrid_3_3")

    # -----------------------------------------------------------------
    # Strategy 6: admissible 3+3 perturbations of reference codes
    # -----------------------------------------------------------------
    for ref in REFERENCE_CODES:
        if ref["ell"] != ell or ref["m"] != m:
            continue
        base_A = ref["A"]
        base_B = ref["B"]
        _add(base_A, base_B, "reference_perturbation_3_3")

        for delta in [-2, -1, 1, 2]:
            for index in range(3):
                for coord in [0, 1]:
                    new_A = [list(term) for term in base_A]
                    limit = ell if coord == 0 else m
                    new_A[index][coord] = (new_A[index][coord] + delta) % limit
                    _add(
                        [tuple(term) for term in new_A],
                        base_B,
                        "reference_perturbation_3_3",
                    )

                    new_B = [list(term) for term in base_B]
                    new_B[index][coord] = (new_B[index][coord] + delta) % limit
                    _add(
                        base_A,
                        [tuple(term) for term in new_B],
                        "reference_perturbation_3_3",
                    )

    # Preserve safety-net ordering, then take one candidate per family bucket
    # per pass.  Per-split and per-family limits prevent representation collapse.
    candidates = []
    split_counts = {split: 0 for split in CHALLENGE_TERM_SPLITS}
    family_counts = {}
    safety_keys = [
        key for key in buckets
        if key[1] == "00_safety_net"
    ]
    for key in safety_keys:
        split, family = key
        for candidate in buckets[key]:
            candidates.append(candidate)
            split_counts[split] += 1
            family_counts[family] = family_counts.get(family, 0) + 1

    active_keys = sorted(key for key in buckets if key not in safety_keys)
    positions = {key: 0 for key in active_keys}
    while len(candidates) < max_candidates:
        made_progress = False
        for key in active_keys:
            split, family = key
            position = positions[key]
            if position >= len(buckets[key]):
                continue
            if split_counts[split] >= per_split_limit:
                continue
            if family_counts.get(family, 0) >= per_family_limit:
                continue
            candidates.append(buckets[key][position])
            positions[key] += 1
            split_counts[split] += 1
            family_counts[family] = family_counts.get(family, 0) + 1
            made_progress = True
            if len(candidates) >= max_candidates:
                break
        if not made_progress:
            break

    return candidates
# EVOLVE-BLOCK-END
