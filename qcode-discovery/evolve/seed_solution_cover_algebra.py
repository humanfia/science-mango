"""Seed generator for the cover/algebra-mechanism BB-code campaign.

The evolved block proposes mechanisms.  The immutable helpers outside that
block enforce the challenge support budget and balance the returned pool by
mechanism and support split, so a large nested loop cannot consume every slot.

``cover`` is a campaign label, not a proof claim.  Most families below are
deterministic algebraic/geometric heuristics.  Only candidates emitted through
``_lift_quotient_pair`` have the narrower, mechanically checked property that
their target-torus supports project to an explicit base quotient support.
Neither that property nor a classifier label proves a distance lower bound.
"""

from __future__ import annotations

from evaluation.algebraic_mechanisms import classify_algebraic_mechanism


CHALLENGE_TERM_SPLITS = frozenset({
    (2, 2),
    (2, 3),
    (3, 2),
    (2, 4),
    (4, 2),
    (3, 3),
})

MECHANISM_ORDER = (
    "affine_orbit",
    "shared_anchor_coset",
    "complementary_diagonal",
    "asymmetric_anchor",
    "unstructured",
)

MAX_SEED_POOL = 300
MAX_SEED_PER_CELL = 25
MAX_SEED_PROPOSALS = 4000
_GUARD_STATE_KEY = "__immutable_seed_guard_state__"

REFERENCE_CODES = (
    (6, 6, ((3, 0), (0, 1), (0, 2)), ((0, 3), (1, 0), (2, 0))),
    (12, 6, ((3, 0), (0, 1), (0, 2)), ((0, 3), (1, 0), (2, 0))),
    (6, 12, ((3, 0), (0, 1), (0, 2)), ((0, 3), (1, 0), (2, 0))),
    (12, 12, ((3, 0), (0, 2), (0, 7)), ((0, 3), (1, 0), (2, 0))),
    (24, 6, ((6, 0), (0, 1), (0, 2)), ((0, 3), (2, 0), (4, 0))),
    (15, 12, ((0, 0), (0, 1), (0, 2)), ((0, 0), (5, 0), (10, 0))),
    (30, 6, ((9, 0), (0, 1), (0, 2)), ((0, 3), (25, 0), (26, 0))),
)

# Deterministic Stage-1 safety fixtures.  Tests rebuild every code and require
# at least three statically eligible examples in every observed mechanism lane
# at both preflight lattices; these hard cases prevent a syntactically diverse
# but entirely k=0/disconnected island from looking healthy.
STAGE1_STATIC_ELIGIBLE_FIXTURES = (
    # 6x6 affine-orbit fixtures.
    (6, 6, ((0, 0), (2, 5), (5, 1)), ((1, 4), (2, 3), (4, 2))),
    (6, 6, ((2, 4), (2, 5), (3, 4)), ((1, 2), (2, 1), (2, 2))),
    (6, 6, ((1, 0), (3, 5), (4, 2)), ((0, 3), (1, 0), (4, 4))),
    # 6x6 unstructured fixtures.
    (6, 6, ((1, 3), (2, 2), (5, 4)), ((0, 3), (2, 5), (5, 1))),
    (6, 6, ((2, 1), (2, 2), (4, 3)), ((0, 0), (0, 2), (5, 4))),
    (6, 6, ((1, 0), (3, 2), (4, 5)), ((0, 3), (1, 3), (5, 0))),
    # 12x6 affine-orbit fixtures.
    (12, 6, ((1, 1), (5, 2), (8, 3)), ((0, 0), (5, 4), (9, 5))),
    (12, 6, ((3, 5), (8, 5), (11, 4)), ((2, 3), (5, 2), (9, 3))),
    (12, 6, ((1, 0), (6, 5), (8, 0)), ((4, 1), (6, 2), (11, 2))),
    # 12x6 unstructured fixtures.
    (12, 6, ((0, 1), (4, 4), (11, 1)), ((1, 2), (6, 2), (11, 4))),
    (12, 6, ((7, 1), (8, 1), (9, 4)), ((2, 1), (2, 5), (3, 4))),
    (12, 6, ((0, 5), (7, 0), (10, 5)), ((0, 1), (5, 1), (7, 4))),
)

# Small quotient definitions used only by the explicit lift path.  The lift
# checker below verifies divisibility and the support projection term by term.
# Other templates in generate_candidates are heuristic mechanism proposals.
QUOTIENT_LIFT_BASES = (
    (
        "bravyi-6x6-support",
        6,
        6,
        ((3, 0), (0, 1), (0, 2)),
        ((0, 3), (1, 0), (2, 0)),
    ),
    (
        "mixed-3x3-support",
        3,
        3,
        ((0, 0), (1, 0), (0, 1)),
        ((0, 0), (1, 1)),
    ),
)


def _normalise_support(terms, ell, m):
    return tuple(sorted({(int(x) % ell, int(y) % m) for x, y in terms}))


def _canonical_candidate_key(a_terms, b_terms, ell, m):
    """Canonicalise common torus translations and exchange of A/B.

    Only exact symmetries used here are quotiented out.  In particular, this
    inexpensive seed guard does not pretend to replace the later Tanner-graph
    equivalence screen.
    """

    A = _normalise_support(a_terms, ell, m)
    B = _normalise_support(b_terms, ell, m)
    anchors = tuple(sorted(set(A).union(B)))
    if not anchors:
        return (A, B) if A <= B else (B, A)
    variants = []
    for anchor_x, anchor_y in anchors:
        shifted_a = tuple(
            sorted(
                ((x - anchor_x) % ell, (y - anchor_y) % m)
                for x, y in A
            )
        )
        shifted_b = tuple(
            sorted(
                ((x - anchor_x) % ell, (y - anchor_y) % m)
                for x, y in B
            )
        )
        variants.append(
            (shifted_a, shifted_b)
            if (shifted_a, shifted_b) <= (shifted_b, shifted_a)
            else (shifted_b, shifted_a)
        )
    return min(variants)


def _lift_quotient_support(
    terms,
    *,
    base_ell,
    base_m,
    ell,
    m,
    fiber_pattern=0,
):
    """Lift one quotient support and verify its projection to the base.

    Each exponent receives a deterministic fibre coordinate.  Reduction
    modulo ``(base_ell, base_m)`` therefore recovers the exact base support.
    This is a checkable support lift, not a claim about code distance.
    """

    if ell % base_ell or m % base_m:
        raise ValueError("target torus must be divisible by the base quotient")
    base = _normalise_support(terms, base_ell, base_m)
    x_fibers = ell // base_ell
    y_fibers = m // base_m
    lifted = tuple(
        sorted(
            (
                (x + base_ell * ((fiber_pattern + index) % x_fibers)) % ell,
                (
                    y
                    + base_m
                    * ((2 * fiber_pattern + index * index) % y_fibers)
                )
                % m,
            )
            for index, (x, y) in enumerate(base)
        )
    )
    projected = _normalise_support(
        ((x % base_ell, y % base_m) for x, y in lifted),
        base_ell,
        base_m,
    )
    if projected != base:
        raise RuntimeError("quotient-support lift failed its projection check")
    return lifted


def _lift_quotient_pair(base, ell, m, *, fiber_pattern=0):
    """Return one verified base-quotient support pair on the target torus."""

    _name, base_ell, base_m, a_terms, b_terms = base
    lifted_a = _lift_quotient_support(
        a_terms,
        base_ell=base_ell,
        base_m=base_m,
        ell=ell,
        m=m,
        fiber_pattern=2 * fiber_pattern,
    )
    lifted_b = _lift_quotient_support(
        b_terms,
        base_ell=base_ell,
        base_m=base_m,
        ell=ell,
        m=m,
        fiber_pattern=2 * fiber_pattern + 1,
    )
    return lifted_a, lifted_b


def _guarded_bucket_add(
    buckets, seen, ell, m, a_terms, b_terms, mechanism
):
    """Enforce immutable challenge gates before one candidate enters a bucket."""

    if mechanism not in MECHANISM_ORDER:
        return False
    guard_state = buckets.setdefault(_GUARD_STATE_KEY, {"proposals": 0})
    if guard_state["proposals"] >= MAX_SEED_PROPOSALS:
        return False
    guard_state["proposals"] += 1
    A = _normalise_support(a_terms, ell, m)
    B = _normalise_support(b_terms, ell, m)
    split = (len(A), len(B))
    if split not in CHALLENGE_TERM_SPLITS or len(A) + len(B) > 6:
        return False
    if A == B:
        return False
    key = _canonical_candidate_key(A, B, ell, m)
    if key in seen:
        return False
    # The caller's label is an intent.  Archive quotas use the immutable
    # classifier's observed mechanism so a mislabeled template cannot capture
    # another island's budget.
    observed_mechanism = classify_algebraic_mechanism(
        A, B, ell=ell, m=m
    )["relation_type"]
    bucket = buckets.setdefault((observed_mechanism, split), [])
    if len(bucket) >= 160:
        return False
    seen.add(key)
    bucket.append(([tuple(term) for term in A], [tuple(term) for term in B]))
    return True


def _balanced_pool(buckets, *, limit=1200, per_cell=100):
    """Round-robin mechanisms, then their support cells, with hard quotas."""

    # Immutable caps remain effective even if an evolved block asks for a much
    # larger return pool.  This bounds downstream construction/evaluation work.
    limit = min(MAX_SEED_POOL, max(0, int(limit)))
    per_cell = min(MAX_SEED_PER_CELL, max(0, int(per_cell)))
    split_order = sorted(CHALLENGE_TERM_SPLITS)
    mechanism_keys = {
        mechanism: [
            (mechanism, split)
            for split in split_order
            if buckets.get((mechanism, split))
        ]
        for mechanism in MECHANISM_ORDER
    }
    keys = [key for values in mechanism_keys.values() for key in values]
    positions = {key: 0 for key in keys}
    cell_cursor = {mechanism: 0 for mechanism in MECHANISM_ORDER}
    output = []
    while len(output) < limit:
        progressed = False
        for mechanism in MECHANISM_ORDER:
            local_keys = mechanism_keys[mechanism]
            if not local_keys:
                continue
            for offset in range(len(local_keys)):
                index = (cell_cursor[mechanism] + offset) % len(local_keys)
                key = local_keys[index]
                position = positions[key]
                if position >= min(per_cell, len(buckets[key])):
                    continue
                output.append(buckets[key][position])
                positions[key] += 1
                cell_cursor[mechanism] = (index + 1) % len(local_keys)
                progressed = True
                break
            if len(output) >= limit:
                break
        if not progressed:
            break
    return output


# EVOLVE-BLOCK-START
def generate_candidates(ell, m):
    """Generate a balanced pool of algebra-mechanism candidate heuristics."""

    from math import gcd, lcm

    buckets = {}
    seen = set()

    def add(A, B, mechanism):
        return _guarded_bucket_add(
            buckets, seen, ell, m, A, B, mechanism
        )

    # Verified quotient-support lifts are a small, auditable lane.  They are
    # present only when the target torus covers the declared base dimensions;
    # the remainder of this generator must not be described as formal lifts.
    for base in QUOTIENT_LIFT_BASES:
        _name, base_ell, base_m, _base_a, _base_b = base
        if ell % base_ell or m % base_m:
            continue
        fiber_count = (ell // base_ell) * (m // base_m)
        for fiber_pattern in range(min(8, max(1, fiber_count))):
            lifted_a, lifted_b = _lift_quotient_pair(
                base, ell, m, fiber_pattern=fiber_pattern
            )
            add(lifted_a, lifted_b, "unstructured")

    for fixture_ell, fixture_m, fixture_a, fixture_b in (
        STAGE1_STATIC_ELIGIBLE_FIXTURES
    ):
        if (fixture_ell, fixture_m) == (ell, m):
            add(fixture_a, fixture_b, "unstructured")

    # Known definitions only keep the cascade alive; their tiny, dedicated
    # bucket cannot dominate a mechanism cell.
    for ref_ell, ref_m, A, B in REFERENCE_CODES:
        if (ref_ell, ref_m) == (ell, m):
            add(A, B, "unstructured")

    primitive_x = [x for x in range(1, min(ell, 12)) if gcd(x, ell) == 1]
    primitive_y = [y for y in range(1, min(m, 12)) if gcd(y, m) == 1]
    if not primitive_x:
        primitive_x = list(range(1, min(ell, 6)))
    if not primitive_y:
        primitive_y = list(range(1, min(m, 6)))
    diagonal = [
        (x, y)
        for x in primitive_x[:6]
        for y in primitive_y[:6]
    ]
    axis = (
        [(x, 0) for x in primitive_x[:8]]
        + [(0, y) for y in primitive_y[:8]]
    )
    shifts = axis + diagonal

    # 1. Affine automorphism/translation covers. Rank-2 trinomials avoid the
    # complementary-line classifier; binomial images keep the same direction.
    for ux in primitive_x[:5]:
        for vy in primitive_y[:5]:
            A3 = [(0, 0), (ux, 0), (0, vy)]
            for sx in range(1, min(ell, 6)):
                for sy in range(1, min(m, 6)):
                    B3 = [
                        ((-x + sx) % ell, (y + sy) % m)
                        for x, y in A3
                    ]
                    add(A3, B3, "affine_orbit")
            A2 = [(0, 0), (ux, vy)]
            for sx, sy in diagonal[:8]:
                B2 = [((x + sx) % ell, (y + sy) % m) for x, y in A2]
                add(A2, B2, "affine_orbit")

    # 2. Shared-anchor/coset covers. A shared primitive difference survives on
    # both sides, while unequal support prevents generic affine equivalence.
    for u in shifts[:14]:
        twice_u = ((2 * u[0]) % ell, (2 * u[1]) % m)
        if twice_u in {(0, 0), u}:
            continue
        for v in diagonal[:14]:
            if v in {(0, 0), u, twice_u}:
                continue
            A2 = [(0, 0), u]
            B3 = [(0, 0), twice_u, v]
            orientation = (
                u[0] + 3 * u[1] + 5 * v[0] + 7 * v[1]
            ) % 2
            if orientation:
                add(B3, A2, "shared_anchor_coset")
            else:
                add(A2, B3, "shared_anchor_coset")
            for w in axis[:8]:
                if w not in set(B3):
                    B4 = B3 + [w]
                    if (orientation + w[0] + w[1]) % 2:
                        add(B4, A2, "shared_anchor_coset")
                    else:
                        add(A2, B4, "shared_anchor_coset")

    # 3. Complementary diagonal covers. Each side is a short orbit on a
    # different primitive line, so this family spans 2+2/2+3/3+2/3+3.
    for u in diagonal[:16]:
        v = (u[1] % ell, (-u[0]) % m)
        if v == (0, 0) or u[0] * v[1] == u[1] * v[0]:
            continue
        Au = [(0, 0), u, ((2 * u[0]) % ell, (2 * u[1]) % m)]
        Bv = [(1 % ell, 1 % m)]
        Bv.extend(
            [
                ((1 + v[0]) % ell, (1 + v[1]) % m),
                ((1 + 2 * v[0]) % ell, (1 + 2 * v[1]) % m),
            ]
        )
        add(Au[:2], Bv[:2], "complementary_diagonal")
        add(Au[:2], Bv, "complementary_diagonal")
        add(Au, Bv[:2], "complementary_diagonal")
        add(Au, Bv, "complementary_diagonal")

    # Rectangular coprime tori can turn a mixed (x,y) step into an orbit of the
    # entire product.  The descriptor intentionally does not call that a
    # one-dimensional line.  Independent horizontal/vertical cyclic subgroups
    # are proper on every non-trivial rectangular target, so these templates
    # keep the complementary lane reachable without relying on a square-only
    # coordinate rotation.
    for ux in primitive_x[:6]:
        for vy in primitive_y[:6]:
            A_axis = [(0, 0), (ux, 0), ((2 * ux) % ell, 0)]
            B_axis = [
                (1 % ell, 1 % m),
                (1 % ell, (1 + vy) % m),
                (1 % ell, (1 + 2 * vy) % m),
            ]
            add(A_axis[:2], B_axis[:2], "complementary_diagonal")
            add(A_axis[:2], B_axis, "complementary_diagonal")
            add(A_axis, B_axis[:2], "complementary_diagonal")
            add(A_axis, B_axis, "complementary_diagonal")

    # 4. Asymmetric anchors. Only one side spans rank two and the supports use
    # disjoint anchors/directions, avoiding the stronger shared-coset rule.
    for u in axis[:12]:
        for v in diagonal[:12]:
            if u == v:
                continue
            A3 = [(0, 0), u, v]
            anchor = ((v[0] + 2) % ell, (v[1] + 2) % m)
            direction = (u[1] % ell, u[0] % m)
            if direction == (0, 0):
                continue
            B2 = [
                anchor,
                ((anchor[0] + direction[0]) % ell,
                 (anchor[1] + direction[1]) % m),
            ]
            orientation = (
                u[0] + 3 * u[1] + 5 * v[0] + 7 * v[1]
            ) % 2
            if orientation:
                add(B2, A3, "asymmetric_anchor")
            else:
                add(A3, B2, "asymmetric_anchor")
            extra = ((u[0] + v[0]) % ell, (u[1] + v[1]) % m)
            if orientation:
                add(A3 + [extra], B2, "asymmetric_anchor")
            else:
                add(B2, A3 + [extra], "asymmetric_anchor")

    # 5. Mechanism-changing restarts: two rank-2 supports with no prescribed
    # affine/shared relationship. These populate the unstructured escape lane.
    # First partition short cyclic orbits into disjoint supports.  The common
    # cyclic span prevents the complementary-line rule, while unequal support
    # shapes prevent affine equality.  These are still heuristic templates,
    # not quotient-cover certificates.
    orbit_directions = [
        (x, y)
        for x in range(ell)
        for y in range(m)
        if (x, y) != (0, 0)
        and lcm(ell // gcd(ell, x), m // gcd(m, y)) >= 6
    ][:80]
    for index, (dx, dy) in enumerate(orbit_directions):
        orbit = [
            ((step * dx) % ell, (step * dy) % m)
            for step in range(6)
        ]
        if len(set(orbit)) != 6:
            continue
        A2 = [orbit[0], orbit[5]]
        B3 = [orbit[1], orbit[2], orbit[3]]
        B4 = [orbit[1], orbit[2], orbit[3], orbit[4]]
        if index % 2:
            add(B3, A2, "unstructured")
            add(A2, B4, "unstructured")
        else:
            add(A2, B3, "unstructured")
            add(B4, A2, "unstructured")
        add(
            [orbit[0], orbit[1], orbit[3]],
            [orbit[2], orbit[4], orbit[5]],
            "unstructured",
        )

    restart_templates = [
        (
            [(1, 2), (0, 4), (2, 4)],
            [(1, 1), (5, 1), (4, 4)],
        ),
        (
            [(5, 0), (4, 0), (2, 1)],
            [(1, 0), (5, 1), (0, 1)],
        ),
        (
            [(4, 0), (2, 1), (4, 3)],
            [(0, 1), (5, 3), (2, 2)],
        ),
        (
            [(3, 0), (1, 1), (3, 3)],
            [(5, 2), (4, 3), (2, 0)],
        ),
    ]
    for base_A, base_B in restart_templates:
        for sx in range(min(ell, 6)):
            for sy in range(min(m, 6)):
                A = [((x + sx) % ell, (y + sy) % m) for x, y in base_A]
                # Offset B differently so shared anchors are not introduced by
                # a common global translation.
                B = [
                    ((x + 2 * sx + 1) % ell, (y + 3 * sy + 1) % m)
                    for x, y in base_B
                ]
                add(A, B, "unstructured")
    for index, u in enumerate(shifts[:18]):
        for v in diagonal[index % max(1, len(diagonal)):][:1]:
            A = [(0, 0), u, v]
            for w in diagonal[4:18]:
                B = [
                    ((w[0] + 1) % ell, (w[1] + 2) % m),
                    ((w[0] + 3) % ell, (w[1] + 1) % m),
                    ((w[0] + u[0] + 2) % ell,
                     (w[1] + v[1] + 3) % m),
                ]
                add(A, B, "unstructured")

    return _balanced_pool(buckets, limit=300, per_cell=25)
# EVOLVE-BLOCK-END
