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
SUPPORTED_GEOMETRY_CONTRACTS = frozenset({
    LEGACY_GEOMETRY_CONTRACT,
    TWISTED_TORUS_GEOMETRY_CONTRACT,
})
TWISTED_TORUS_REPRESENTATION_ID = "css-bb-twisted-torus-generator-v1"
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


def _ordered_factor_lattices(volume: int) -> tuple[tuple[int, int], ...]:
    """Return every ordered ``ell*m=volume`` shape with both axes nontrivial."""

    if isinstance(volume, bool) or not isinstance(volume, int) or volume < 4:
        raise ValueError("cell volume must be an integer of at least four")
    return tuple(
        (ell, volume // ell)
        for ell in range(2, volume)
        if volume % ell == 0 and volume // ell >= 2
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
TWISTED_STAGE2_FITNESS_LATTICES: tuple[tuple[int, int], ...] = (
    (12, 6),   # n=144
    (10, 10),  # n=200
    (12, 12),  # n=288
    (6, 30),   # n=360; includes the q=6 literature lane
)


def lattices_for_geometry_contract(
    contract: str,
) -> tuple[tuple[int, int], ...]:
    """Return the Pareto-first immutable lattice list for one representation."""

    if contract not in SUPPORTED_GEOMETRY_CONTRACTS:
        raise ValueError(f"unsupported search geometry contract: {contract!r}")
    targets = (
        TWISTED_TARGET_LATTICES
        if contract == TWISTED_TORUS_GEOMETRY_CONTRACT
        else LEGACY_TARGET_LATTICES
    )
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
    return LEGACY_STAGE2_FITNESS_LATTICES


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
    list so no twist stratum can disappear through evolutionary collapse.
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
TARGET_LATTICES = (
    TWISTED_TARGET_LATTICES
    if ACTIVE_GEOMETRY_CONTRACT == TWISTED_TORUS_GEOMETRY_CONTRACT
    else LEGACY_TARGET_LATTICES
)
EVOLUTION_LATTICES = lattices_for_geometry_contract(ACTIVE_GEOMETRY_CONTRACT)
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
    "EVOLUTION_LATTICES",
    "FINAL_GATE_PARETO_LATTICES",
    "LEGACY_GEOMETRY_CONTRACT",
    "LEGACY_PRODUCTION_REPRESENTATION_IDS",
    "LEGACY_STAGE2_FITNESS_LATTICES",
    "LEGACY_TARGET_LATTICES",
    "REPRESENTATION_GEOMETRY_CONTRACTS",
    "SEARCH_GEOMETRY_CONTRACT_ENV",
    "SUPPORTED_GEOMETRY_CONTRACTS",
    "TARGET_CELL_VOLUMES",
    "TARGET_LATTICES",
    "TWISTED_TARGET_LATTICES",
    "TWISTED_STAGE2_FITNESS_LATTICES",
    "TWISTED_MIN_CANDIDATES_PER_TWIST",
    "TWISTED_TORUS_REPRESENTATION_ID",
    "TWISTED_TORUS_GEOMETRY_CONTRACT",
    "allowed_twists",
    "geometry_contract_for_representation",
    "lattices_for_geometry_contract",
    "stage2_deep_lattices_for_geometry_contract",
    "stage2_fitness_lattices_for_geometry_contract",
]
