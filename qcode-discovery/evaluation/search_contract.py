"""Immutable lattice coverage contract for BB-code evolution.

The evolved seed and its evaluator must agree on every lattice on which the
generator is called.  Keeping this contract outside the mutable evolve block
prevents a seed/evaluator list drift from making an entire lattice family
unreachable.
"""

from __future__ import annotations


# Small fixed-coordinate Pareto reference lattices accepted by the final gate.
# They are evaluated first so their candidates are persisted before a later
# large lattice can consume the evaluator wall budget.
FINAL_GATE_PARETO_LATTICES: tuple[tuple[int, int], ...] = (
    (6, 6),
    (15, 3),
    (9, 6),
)

# Formal target lattice dimensions declared by the evolutionary search.
TARGET_LATTICES: tuple[tuple[int, int], ...] = (
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

# Full generator-call coverage.  Preserve the Pareto-first ordering while
# de-duplicating any future overlap with the formal target list.
EVOLUTION_LATTICES: tuple[tuple[int, int], ...] = (
    *FINAL_GATE_PARETO_LATTICES,
    *tuple(
        lattice
        for lattice in TARGET_LATTICES
        if lattice not in FINAL_GATE_PARETO_LATTICES
    ),
)
