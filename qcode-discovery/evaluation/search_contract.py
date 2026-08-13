"""Immutable geometry coverage contract for BB-code evolution.

The legacy campaigns evaluate a deliberately small list of rectangular
``(ell, m)`` tori.  The twisted-torus representation uses a separate,
explicitly selected contract containing every non-degenerate ordered factor
pair for the target cell volumes.  Keeping the selection outside the mutable
evolve block prevents an evolved generator from silently starving a geometry
lane.

The active contract is selected in the private evaluator process through
``QCODE_SEARCH_GEOMETRY_CONTRACT``.  The launcher is responsible for deriving
that value from the signed campaign representation; ordinary imports retain
the historical contract.
"""

from __future__ import annotations

import os
from types import MappingProxyType


SEARCH_GEOMETRY_CONTRACT_ENV = "QCODE_SEARCH_GEOMETRY_CONTRACT"
LEGACY_GEOMETRY_CONTRACT = "rectangular-v1"
TWISTED_TORUS_GEOMETRY_CONTRACT = "twisted-torus-v1"
PUBLISHED_VOLUME_GEOMETRY_CONTRACT = "twisted-torus-published-volume-v2"
PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT = (
    "twisted-torus-published-volume-ansatz-v3"
)
SUPPORTED_GEOMETRY_CONTRACTS = frozenset({
    LEGACY_GEOMETRY_CONTRACT,
    TWISTED_TORUS_GEOMETRY_CONTRACT,
    PUBLISHED_VOLUME_GEOMETRY_CONTRACT,
    PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
})
TWISTED_TORUS_REPRESENTATION_ID = "css-bb-twisted-torus-generator-v1"
PUBLISHED_VOLUME_REPRESENTATION_ID = (
    "css-bb-twisted-torus-published-volume-generator-v2"
)
PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID = (
    "css-bb-twisted-torus-published-volume-ansatz-generator-v3"
)
TWISTED_GEOMETRY_CONTRACTS = frozenset({
    TWISTED_TORUS_GEOMETRY_CONTRACT,
    PUBLISHED_VOLUME_GEOMETRY_CONTRACT,
    PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
})
TWISTED_MIN_CANDIDATES_PER_TWIST = 3
LEGACY_PRODUCTION_REPRESENTATION_IDS = frozenset({
    "css-bb-cover-algebra-generator-v2",
    "css-bb-novel-ansatz-generator-v2",
})

# This mapping is part of the launch-bound evaluator dependency graph.  The
# Humanize launcher calls the helper below instead of carrying a second local
# table, so a prepared/resumed transaction cannot silently reinterpret the
# same persisted representation identifier under a different geometry env.
REPRESENTATION_GEOMETRY_CONTRACTS = MappingProxyType({
    "css-bb-cover-algebra-generator-v2": LEGACY_GEOMETRY_CONTRACT,
    "css-bb-novel-ansatz-generator-v2": LEGACY_GEOMETRY_CONTRACT,
    TWISTED_TORUS_REPRESENTATION_ID: TWISTED_TORUS_GEOMETRY_CONTRACT,
    PUBLISHED_VOLUME_REPRESENTATION_ID: PUBLISHED_VOLUME_GEOMETRY_CONTRACT,
    PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID: (
        PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT
    ),
})

PUBLISHED_VOLUME_GEOMETRY_CONTRACTS = frozenset({
    PUBLISHED_VOLUME_GEOMETRY_CONTRACT,
    PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
})


def geometry_contract_for_representation(
    representation_id: object,
) -> str | None:
    """Return the opt-in geometry contract for a frozen representation ID.

    Unknown or absent representation IDs intentionally return ``None`` so
    legacy and schema-v2 callers retain their historical rectangular
    behavior.  A geometry-aware schema-v3 launcher separately requires the
    exact twisted representation.  The two production schema-v2 IDs are also
    documented explicitly, while only the schema-v3 representation selects
    the expanded contract.
    """

    if not isinstance(representation_id, str):
        return None
    return REPRESENTATION_GEOMETRY_CONTRACTS.get(representation_id)

# Small fixed-coordinate Pareto reference lattices accepted by the final gate.
# They are evaluated first so their candidates are persisted before a later
# large lattice can consume the evaluator wall budget.
FINAL_GATE_PARETO_LATTICES: tuple[tuple[int, int], ...] = (
    (6, 6),
    (15, 3),
    (9, 6),
)

# Historical target dimensions.  Do not expand this tuple in place: legacy
# checkpoints and preflight journals bind its ordering.
LEGACY_TARGET_LATTICES: tuple[tuple[int, int], ...] = (
    # n=144: ell*m = 72
    (12, 6),
    (6, 12),
    (9, 8),
    (8, 9),
    (24, 3),
    (36, 2),
    # n=200: ell*m = 100
    (10, 10),
    (20, 5),
    (25, 4),
    (50, 2),
    # n=288: ell*m = 144
    (12, 12),
    (16, 9),
    (18, 8),
    (24, 6),
    # n=360: ell*m = 180
    (15, 12),
    (18, 10),
    (20, 9),
    (30, 6),
)

TARGET_CELL_VOLUMES: tuple[int, ...] = (72, 100, 144, 180)

# The first twisted campaign covered four historical benchmark volumes.  This
# fresh, checkpoint-incompatible contract targets the *different* torus
# volumes where Liang--Liu--Song--Chen report exact weight-six codes with
# k*d^2/n > 12.  Every non-degenerate ordered factor shape is covered, rather
# than only the published HNF representative, so the experiment measures a
# real geometry expansion around those fertile volumes.  Volume 144 remains a
# Stage-2 calibration lane but is not redundantly rescanned here.  The prime
# volume 127 has the intentional published thin shape (1,127,q=25).  This is
# a bounded, paper-representative lane: the contract does not claim that the
# omitted q labels are equivalent or that it fully covers the prime-volume
# geometry.  Keeping that distinction explicit prevents a finite experiment
# budget from being mistaken for a family-level equivalence statement.
PUBLISHED_VOLUME_CELL_VOLUMES: tuple[int, ...] = (
    105, 124, 126, 127, 132, 147, 170,
)
PUBLISHED_VOLUME_THIN_LATTICE = (1, 127)
PUBLISHED_VOLUME_THIN_TWIST = 25
PUBLISHED_VOLUME_CONTINUITY_LATTICE = (12, 12)
PUBLISHED_VOLUME_CONTINUITY_TWIST = 0


def _ordered_factor_lattices(volume: int) -> tuple[tuple[int, int], ...]:
    """Return every ordered ``ell*m=volume`` shape with both axes nontrivial."""

    if isinstance(volume, bool) or not isinstance(volume, int) or volume < 4:
        raise ValueError("cell volume must be an integer of at least four")
    return tuple(
        (ell, volume // ell)
        for ell in range(2, volume)
        if volume % ell == 0 and volume // ell >= 2
    )


PUBLISHED_VOLUME_TARGET_LATTICES: tuple[tuple[int, int], ...] = (
    PUBLISHED_VOLUME_THIN_LATTICE,
    *(
        lattice
        for volume in PUBLISHED_VOLUME_CELL_VOLUMES
        if volume != 127
        for lattice in _ordered_factor_lattices(volume)
    ),
)


# All ordered HNF diagonal shapes for the four formal target lengths.  A twist
# q then selects the relation lattice <(0,m),(ell,q)>.  Ordered shapes are
# intentional: swapping the two ambient axes changes which boundary carries
# the shear and is part of the search representation, even when a later
# Tanner-isomorphism screen proves two resulting codes equivalent.
TWISTED_TARGET_LATTICES: tuple[tuple[int, int], ...] = tuple(
    lattice
    for volume in TARGET_CELL_VOLUMES
    for lattice in _ordered_factor_lattices(volume)
)

# Blocking distance work is deliberately bounded to representative shapes.
# This list is shared by the evaluator and the managed launcher because Stage
# 2 completion markers record its exact cardinality.  Keeping the two views in
# one launch-bound module prevents a valid fresh-representation marker from
# being rejected by a stale launcher-side integer.
LEGACY_STAGE2_FITNESS_LATTICES: tuple[tuple[int, int], ...] = (
    (12, 6),
    (6, 12),
    (12, 12),
    (24, 6),
    (15, 12),
    (30, 6),
    (16, 9),
    (18, 8),
)
LEGACY_STAGE1_FITNESS_LATTICES: tuple[tuple[int, int], ...] = (
    (6, 6),
    (12, 6),
)
TWISTED_STAGE1_FITNESS_LATTICES: tuple[tuple[int, int], ...] = (
    (12, 6),
    (10, 10),
    (12, 12),
    (6, 30),
)
PUBLISHED_VOLUME_STAGE1_FITNESS_LATTICES: tuple[tuple[int, int], ...] = (
    (12, 12),  # v1 exact-continuity control
    (5, 21),   # smallest newly covered published winner volume
    (2, 62),   # elongated strong-shear stress lane
    (5, 34),   # largest published winner volume
)
TWISTED_STAGE2_FITNESS_LATTICES: tuple[tuple[int, int], ...] = (
    (12, 6),   # n=144
    (10, 10),  # n=200
    (12, 12),  # n=288
    (6, 30),   # n=360; includes the q=6 literature lane
)
PUBLISHED_VOLUME_STAGE2_FITNESS_LATTICES: tuple[tuple[int, int], ...] = (
    (5, 21),   # n=210
    (2, 62),   # n=248
    (7, 18),   # n=252
    (1, 127),  # n=254; prime-volume published anchor
    (2, 66),   # n=264
    (12, 12),  # n=288; v1 continuity calibration
    (7, 21),   # n=294
    (5, 34),   # n=340
)


def is_twisted_geometry_contract(contract: object) -> bool:
    """Return whether ``contract`` carries q-stratified twisted geometry."""

    return isinstance(contract, str) and contract in TWISTED_GEOMETRY_CONTRACTS


def lattices_for_geometry_contract(
    contract: str,
) -> tuple[tuple[int, int], ...]:
    """Return the Pareto-first immutable lattice list for one representation."""

    if contract not in SUPPORTED_GEOMETRY_CONTRACTS:
        raise ValueError(f"unsupported search geometry contract: {contract!r}")
    if contract == TWISTED_TORUS_GEOMETRY_CONTRACT:
        targets = TWISTED_TARGET_LATTICES
    elif contract in PUBLISHED_VOLUME_GEOMETRY_CONTRACTS:
        targets = PUBLISHED_VOLUME_TARGET_LATTICES
    else:
        targets = LEGACY_TARGET_LATTICES
    return (
        *FINAL_GATE_PARETO_LATTICES,
        *(lattice for lattice in targets if lattice not in FINAL_GATE_PARETO_LATTICES),
    )


def stage2_fitness_lattices_for_geometry_contract(
    contract: str,
) -> tuple[tuple[int, int], ...]:
    """Return the bounded distance-fitness representatives for a contract."""

    if contract not in SUPPORTED_GEOMETRY_CONTRACTS:
        raise ValueError(f"unsupported search geometry contract: {contract!r}")
    if contract == TWISTED_TORUS_GEOMETRY_CONTRACT:
        return TWISTED_STAGE2_FITNESS_LATTICES
    if contract in PUBLISHED_VOLUME_GEOMETRY_CONTRACTS:
        return PUBLISHED_VOLUME_STAGE2_FITNESS_LATTICES
    return LEGACY_STAGE2_FITNESS_LATTICES


def stage1_fitness_lattices_for_geometry_contract(
    contract: str,
) -> tuple[tuple[int, int], ...]:
    """Return the bounded quick-fitness probes for one fresh representation."""

    if contract not in SUPPORTED_GEOMETRY_CONTRACTS:
        raise ValueError(f"unsupported search geometry contract: {contract!r}")
    if contract == TWISTED_TORUS_GEOMETRY_CONTRACT:
        return TWISTED_STAGE1_FITNESS_LATTICES
    if contract in PUBLISHED_VOLUME_GEOMETRY_CONTRACTS:
        return PUBLISHED_VOLUME_STAGE1_FITNESS_LATTICES
    return LEGACY_STAGE1_FITNESS_LATTICES


def stage2_deep_lattices_for_geometry_contract(
    contract: str,
) -> tuple[tuple[int, int], ...]:
    """Return the Pareto-first Stage-2 completion-marker lattice contract."""

    fitness = stage2_fitness_lattices_for_geometry_contract(contract)
    return (
        *FINAL_GATE_PARETO_LATTICES,
        *(lattice for lattice in fitness if lattice not in FINAL_GATE_PARETO_LATTICES),
    )


def allowed_twists(ell: int, m: int, *, contract: str) -> tuple[int, ...]:
    """Return every twist required for one contracted outer lattice.

    For the quotient relations ``y^m=1`` and ``x^ell*y^q=1``, replacing ``q``
    by ``q+m`` gives the same relation lattice.  The complete canonical range
    is therefore ``0 <= q < m``.  The immutable wrapper, not the LLM, owns this
    list so no contracted twist stratum can disappear through evolutionary
    collapse.  The published-volume thin lane is deliberately restricted to
    the paper representative q=25; no equivalence with omitted q values is
    asserted.  Its historical ``(12,12)`` continuity control is likewise
    restricted to the published q=0 construction.
    """

    if (
        isinstance(ell, bool)
        or not isinstance(ell, int)
        or ell <= 0
        or isinstance(m, bool)
        or not isinstance(m, int)
        or m <= 0
    ):
        raise ValueError("ell and m must be positive integers")
    if contract not in SUPPORTED_GEOMETRY_CONTRACTS:
        raise ValueError(f"unsupported search geometry contract: {contract!r}")
    if contract == LEGACY_GEOMETRY_CONTRACT:
        return (0,)
    if (
        contract in PUBLISHED_VOLUME_GEOMETRY_CONTRACTS
        and (ell, m) == PUBLISHED_VOLUME_THIN_LATTICE
    ):
        return (PUBLISHED_VOLUME_THIN_TWIST,)
    if (
        contract in PUBLISHED_VOLUME_GEOMETRY_CONTRACTS
        and (ell, m) == PUBLISHED_VOLUME_CONTINUITY_LATTICE
    ):
        return (PUBLISHED_VOLUME_CONTINUITY_TWIST,)
    return tuple(range(m))


ACTIVE_GEOMETRY_CONTRACT = os.environ.get(
    SEARCH_GEOMETRY_CONTRACT_ENV,
    LEGACY_GEOMETRY_CONTRACT,
)
if ACTIVE_GEOMETRY_CONTRACT not in SUPPORTED_GEOMETRY_CONTRACTS:
    raise RuntimeError(
        f"{SEARCH_GEOMETRY_CONTRACT_ENV} selects unsupported contract "
        f"{ACTIVE_GEOMETRY_CONTRACT!r}"
    )

# Backward-compatible names used throughout the evaluator.  In the ordinary
# process these remain byte-for-byte equivalent to the historical values; a
# signed twisted-torus launch selects the expanded contract before import.
if ACTIVE_GEOMETRY_CONTRACT == TWISTED_TORUS_GEOMETRY_CONTRACT:
    TARGET_LATTICES = TWISTED_TARGET_LATTICES
elif ACTIVE_GEOMETRY_CONTRACT in PUBLISHED_VOLUME_GEOMETRY_CONTRACTS:
    TARGET_LATTICES = PUBLISHED_VOLUME_TARGET_LATTICES
else:
    TARGET_LATTICES = LEGACY_TARGET_LATTICES
EVOLUTION_LATTICES = lattices_for_geometry_contract(ACTIVE_GEOMETRY_CONTRACT)
ACTIVE_STAGE1_FITNESS_LATTICES = stage1_fitness_lattices_for_geometry_contract(
    ACTIVE_GEOMETRY_CONTRACT
)
ACTIVE_STAGE2_FITNESS_LATTICES = stage2_fitness_lattices_for_geometry_contract(
    ACTIVE_GEOMETRY_CONTRACT
)
ACTIVE_STAGE2_DEEP_LATTICES = stage2_deep_lattices_for_geometry_contract(
    ACTIVE_GEOMETRY_CONTRACT
)


__all__ = [
    "ACTIVE_GEOMETRY_CONTRACT",
    "ACTIVE_STAGE2_DEEP_LATTICES",
    "ACTIVE_STAGE2_FITNESS_LATTICES",
    "ACTIVE_STAGE1_FITNESS_LATTICES",
    "EVOLUTION_LATTICES",
    "FINAL_GATE_PARETO_LATTICES",
    "LEGACY_GEOMETRY_CONTRACT",
    "LEGACY_PRODUCTION_REPRESENTATION_IDS",
    "LEGACY_STAGE1_FITNESS_LATTICES",
    "LEGACY_STAGE2_FITNESS_LATTICES",
    "LEGACY_TARGET_LATTICES",
    "PUBLISHED_VOLUME_GEOMETRY_CONTRACT",
    "PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT",
    "PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID",
    "PUBLISHED_VOLUME_CELL_VOLUMES",
    "PUBLISHED_VOLUME_CONTINUITY_LATTICE",
    "PUBLISHED_VOLUME_CONTINUITY_TWIST",
    "PUBLISHED_VOLUME_REPRESENTATION_ID",
    "PUBLISHED_VOLUME_GEOMETRY_CONTRACTS",
    "PUBLISHED_VOLUME_STAGE1_FITNESS_LATTICES",
    "PUBLISHED_VOLUME_STAGE2_FITNESS_LATTICES",
    "PUBLISHED_VOLUME_TARGET_LATTICES",
    "PUBLISHED_VOLUME_THIN_LATTICE",
    "PUBLISHED_VOLUME_THIN_TWIST",
    "REPRESENTATION_GEOMETRY_CONTRACTS",
    "SEARCH_GEOMETRY_CONTRACT_ENV",
    "SUPPORTED_GEOMETRY_CONTRACTS",
    "TARGET_CELL_VOLUMES",
    "TARGET_LATTICES",
    "TWISTED_TARGET_LATTICES",
    "TWISTED_STAGE2_FITNESS_LATTICES",
    "TWISTED_STAGE1_FITNESS_LATTICES",
    "TWISTED_MIN_CANDIDATES_PER_TWIST",
    "TWISTED_TORUS_REPRESENTATION_ID",
    "TWISTED_GEOMETRY_CONTRACTS",
    "TWISTED_TORUS_GEOMETRY_CONTRACT",
    "allowed_twists",
    "geometry_contract_for_representation",
    "is_twisted_geometry_contract",
    "lattices_for_geometry_contract",
    "stage1_fitness_lattices_for_geometry_contract",
    "stage2_deep_lattices_for_geometry_contract",
    "stage2_fitness_lattices_for_geometry_contract",
]
