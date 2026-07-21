"""Verify constant-monomial (CM) code properties claimed in the paper.

Paper claims (Section V-D, lines ~600-618):
- 87 of 154 verified codes are constant-monomial (A depends only on y, B on x,
  both with constant terms, or vice versa)
- All 87 CM codes have MILP distance d in {2, 4}
- (12,6) and (6,12): all CM codes have d=2
- (15,12), (30,6), (24,6), (12,12): mixed d values (d=2 or d=4 depending on
  the specific polynomial pair)
"""
import json
from collections import Counter, defaultdict
from pathlib import Path


def load_catalog():
    path = Path(__file__).parent.parent / "results" / "ilp_catalog.json"
    with open(path) as f:
        catalog = json.load(f)
    all_codes = []
    for key, codes in catalog.items():
        for code in codes:
            all_codes.append(code)
    return all_codes


def is_constant_monomial(code):
    """A code is CM if one poly depends only on y with a constant term,
    and the other depends only on x with a constant term."""
    A = code["A"]
    B = code["B"]

    def only_y_with_const(terms):
        all_x_zero = all(t[0] == 0 for t in terms)
        has_const = any(t[0] == 0 and t[1] == 0 for t in terms)
        return all_x_zero and has_const

    def only_x_with_const(terms):
        all_y_zero = all(t[1] == 0 for t in terms)
        has_const = any(t[0] == 0 and t[1] == 0 for t in terms)
        return all_y_zero and has_const

    # Case 1: A only-y, B only-x
    case1 = only_y_with_const(A) and only_x_with_const(B)
    # Case 2: A only-x, B only-y (swapped)
    case2 = only_x_with_const(A) and only_y_with_const(B)

    return case1 or case2


def get_cm_codes():
    """Load catalog and return CM codes."""
    all_codes = load_catalog()
    return [c for c in all_codes if is_constant_monomial(c)]


def test_cm_count_is_87():
    """Verify there are exactly 87 constant-monomial codes."""
    all_codes = load_catalog()
    cm_codes = [c for c in all_codes if is_constant_monomial(c)]
    print(f"\nTotal codes in catalog: {len(all_codes)}")
    print(f"Constant-monomial codes: {len(cm_codes)}")
    print(f"Non-CM codes: {len(all_codes) - len(cm_codes)}")
    assert len(cm_codes) == 87, f"Expected 87 CM codes, got {len(cm_codes)}"


def test_all_cm_codes_have_d_in_2_or_4():
    """Every CM code must have ilp_d in {2, 4}."""
    cm_codes = get_cm_codes()
    violations = [c for c in cm_codes if c["ilp_d"] not in (2, 4)]
    for v in violations:
        print(f"  VIOLATION: {v['label']} at ({v['ell']},{v['m']}): "
              f"ilp_d={v['ilp_d']}, A={v['A']}, B={v['B']}")
    assert len(violations) == 0, f"{len(violations)} CM codes have d not in {{2, 4}}"


def test_cm_distance_distribution():
    """Report d-value distribution by lattice and verify overall structure."""
    cm_codes = get_cm_codes()

    lattice_d = defaultdict(list)
    for c in cm_codes:
        lattice = (c["ell"], c["m"])
        lattice_d[lattice].append(c["ilp_d"])

    print("\n=== CM code d-value distribution by lattice ===")
    for lattice in sorted(lattice_d.keys()):
        ds = lattice_d[lattice]
        counts = Counter(ds)
        print(f"  ({lattice[0]},{lattice[1]}): {len(ds)} codes, "
              f"d-values: {dict(sorted(counts.items()))}")

    # Overall distribution
    d_dist = Counter(c["ilp_d"] for c in cm_codes)
    print(f"\nOverall d distribution: {dict(sorted(d_dist.items()))}")
    assert set(d_dist.keys()) == {2, 4}, \
        f"Expected d values {{2, 4}}, got {set(d_dist.keys())}"


def test_lattice_12_6_all_d2():
    """All CM codes at (12,6) have d=2."""
    cm_codes = get_cm_codes()
    codes_at = [c for c in cm_codes if (c["ell"], c["m"]) == (12, 6)]
    assert len(codes_at) > 0, "No CM codes at (12,6)"
    for c in codes_at:
        assert c["ilp_d"] == 2, \
            f"CM code at (12,6) has d={c['ilp_d']}, expected 2: A={c['A']}, B={c['B']}"
    print(f"\n(12,6): {len(codes_at)} CM codes, all d=2 -- PASS")


def test_lattice_6_12_all_d2():
    """All CM codes at (6,12) have d=2."""
    cm_codes = get_cm_codes()
    codes_at = [c for c in cm_codes if (c["ell"], c["m"]) == (6, 12)]
    assert len(codes_at) > 0, "No CM codes at (6,12)"
    for c in codes_at:
        assert c["ilp_d"] == 2, \
            f"CM code at (6,12) has d={c['ilp_d']}, expected 2: A={c['A']}, B={c['B']}"
    print(f"\n(6,12): {len(codes_at)} CM codes, all d=2 -- PASS")


def test_mixed_lattices_have_both_d_values():
    """Lattices (15,12), (30,6), (24,6), (12,12) have mixed d in {2, 4}."""
    cm_codes = get_cm_codes()
    mixed_lattices = [(15, 12), (30, 6), (24, 6), (12, 12)]

    for ell, m in mixed_lattices:
        codes_at = [c for c in cm_codes if (c["ell"], c["m"]) == (ell, m)]
        if not codes_at:
            continue
        d_values = set(c["ilp_d"] for c in codes_at)
        # All d values must be in {2, 4}
        assert d_values.issubset({2, 4}), \
            f"({ell},{m}): unexpected d values {d_values}"
        # Mixed lattices should have both d=2 and d=4
        assert d_values == {2, 4}, \
            f"({ell},{m}): expected both d=2 and d=4, got {d_values}"
        d_counts = Counter(c["ilp_d"] for c in codes_at)
        print(f"  ({ell},{m}): {len(codes_at)} codes, d-values: {dict(sorted(d_counts.items()))}")

    print("  All mixed lattices have d in {2, 4} -- PASS")
