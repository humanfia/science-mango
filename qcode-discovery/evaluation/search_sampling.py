"""Replayable support samplers for sparse bivariate-bicycle searches.

This module deliberately stays at the representation already supported by
``evaluation.bb_code``: two non-empty lists of ``(x_exp, y_exp)`` monomials in
``F_2[x, y] / (x^ell - 1, y^m - 1)``.  It does not construct codes, estimate
distance, or claim support for arbitrary multivariate/lifted-product codes.

Three small APIs are provided:

``sample_uniform``
    Uniformly choose a configured support split, then choose each support
    uniformly without replacement from the ``ell * m`` monomials.

``sample_structured_frontier``
    Start from a compact registry of certified Pareto examples and explicitly
    labelled unresolved near-frontier supports.  Reuse the support on a
    compatible lattice, then apply monomial translations, unit coordinate
    scalings, an optional A/B exchange, and bounded local mutations.

``sample_mixed``
    Choose between the two samplers with a replayable mixture probability.

Every sampler accepts either a ``numpy.random.Generator`` or an integer seed.
Passing the same seed and arguments gives the same support and metadata.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from typing import Any, Iterable, Sequence, TypeAlias

import numpy as np


Term: TypeAlias = tuple[int, int]
Support: TypeAlias = list[Term]
SupportPair: TypeAlias = tuple[Support, Support]
SampleWithMetadata: TypeAlias = tuple[Support, Support, dict[str, Any]]
RngLike: TypeAlias = np.random.Generator | int | np.integer | None


# These are the sparse splits accepted by the current weight-six challenge
# search.  Each individual polynomial also satisfies bb_code.validate_terms'
# default lower bound of two terms.
DEFAULT_SPLITS: tuple[tuple[int, int], ...] = (
    (2, 2),
    (2, 3),
    (3, 2),
    (2, 4),
    (4, 2),
    (3, 3),
)


@dataclass(frozen=True)
class FrontierTemplate:
    """A sparse BB support used as a parent, not as a distance assertion."""

    label: str
    ell: int
    m: int
    a_terms: tuple[Term, ...]
    b_terms: tuple[Term, ...]
    evidence: str


# Keep this registry intentionally small.  ``certified-pareto`` labels refer to
# known-answer/frontier codes; ``unresolved-near-frontier`` labels only record
# that a short MILP screen left the support interesting.  They are not exact
# distance claims.
FRONTIER_TEMPLATES: tuple[FrontierTemplate, ...] = (
    FrontierTemplate(
        "pareto-72-12-6",
        6,
        6,
        ((3, 0), (0, 1), (0, 2)),
        ((0, 3), (1, 0), (2, 0)),
        "certified-pareto",
    ),
    FrontierTemplate(
        "pareto-90-8-10",
        15,
        3,
        ((9, 0), (0, 1), (0, 2)),
        ((0, 0), (2, 0), (7, 0)),
        "certified-pareto",
    ),
    FrontierTemplate(
        "pareto-108-8-10",
        9,
        6,
        ((3, 0), (0, 1), (0, 2)),
        ((0, 3), (1, 0), (2, 0)),
        "certified-pareto",
    ),
    FrontierTemplate(
        "pareto-144-12-12",
        12,
        6,
        ((3, 0), (0, 1), (0, 2)),
        ((0, 3), (1, 0), (2, 0)),
        "certified-pareto",
    ),
    FrontierTemplate(
        "near-frontier-288-193",
        12,
        12,
        ((3, 0), (2, 0), (0, 7)),
        ((0, 3), (3, 1), (2, 0)),
        "unresolved-near-frontier",
    ),
    FrontierTemplate(
        "pareto-288-12-18",
        12,
        12,
        ((3, 0), (0, 2), (0, 7)),
        ((0, 3), (1, 0), (2, 0)),
        "certified-pareto",
    ),
    FrontierTemplate(
        "near-frontier-144-k2",
        12,
        6,
        ((11, 5), (8, 0), (5, 1), (1, 0)),
        ((9, 4), (3, 1)),
        "unresolved-near-frontier",
    ),
    FrontierTemplate(
        "near-frontier-108-k2",
        9,
        6,
        ((4, 2), (3, 1), (3, 0), (2, 1)),
        ((0, 2), (0, 5)),
        "unresolved-near-frontier",
    ),
    FrontierTemplate(
        "frontier-360-12-24-upper-bound",
        30,
        6,
        ((9, 0), (0, 1), (0, 2)),
        ((0, 3), (25, 0), (26, 0)),
        "known-upper-bound",
    ),
)


def _coerce_rng(rng: RngLike) -> np.random.Generator:
    if isinstance(rng, np.random.Generator):
        return rng
    if rng is None or isinstance(rng, (int, np.integer)):
        return np.random.default_rng(rng)
    raise TypeError("rng must be a numpy.random.Generator, an integer seed, or None")


def _validate_shape(ell: int, m: int) -> tuple[int, int]:
    if isinstance(ell, bool) or isinstance(m, bool):
        raise TypeError("ell and m must be integers")
    if not isinstance(ell, (int, np.integer)) or not isinstance(m, (int, np.integer)):
        raise TypeError("ell and m must be integers")
    ell, m = int(ell), int(m)
    if ell < 2 or m < 2:
        raise ValueError("ell and m must both be at least 2")
    return ell, m


def _validate_splits(
    splits: Iterable[tuple[int, int]],
    *,
    cells: int,
) -> tuple[tuple[int, int], ...]:
    normalized: list[tuple[int, int]] = []
    for split in splits:
        if len(split) != 2:
            raise ValueError("support splits must be (A_count, B_count) pairs")
        a_count, b_count = int(split[0]), int(split[1])
        if a_count < 2 or b_count < 2:
            raise ValueError("each BB support must contain at least two terms")
        if a_count + b_count > 6:
            raise ValueError("total BB support weight must be at most six")
        if a_count > cells or b_count > cells:
            raise ValueError("support split exceeds the number of lattice monomials")
        normalized.append((a_count, b_count))
    if not normalized:
        raise ValueError("at least one support split is required")
    return tuple(normalized)


def _draw_support(
    rng: np.random.Generator,
    ell: int,
    m: int,
    count: int,
) -> Support:
    choices = rng.choice(ell * m, size=count, replace=False)
    return sorted((int(value // m), int(value % m)) for value in choices)


def _result(
    a_terms: Support,
    b_terms: Support,
    metadata: dict[str, Any],
    *,
    return_metadata: bool,
) -> SupportPair | SampleWithMetadata:
    # Return fresh lists so callers can safely mutate a sample without
    # modifying the template registry or another result.
    a_copy = list(a_terms)
    b_copy = list(b_terms)
    if return_metadata:
        return a_copy, b_copy, metadata
    return a_copy, b_copy


def sample_uniform(
    ell: int,
    m: int,
    *,
    rng: RngLike = None,
    splits: Sequence[tuple[int, int]] = DEFAULT_SPLITS,
    return_metadata: bool = False,
) -> SupportPair | SampleWithMetadata:
    """Sample sparse A/B supports uniformly within a selected split.

    The split itself is selected uniformly from ``splits``.  Conditional on
    that split, A and B are sampled independently and uniformly from all
    supports of the requested size.  A and B may share monomials; duplicates
    within either polynomial are impossible.
    """

    ell, m = _validate_shape(ell, m)
    generator = _coerce_rng(rng)
    valid_splits = _validate_splits(splits, cells=ell * m)
    split_index = int(generator.integers(len(valid_splits)))
    a_count, b_count = valid_splits[split_index]
    a_terms = _draw_support(generator, ell, m, a_count)
    b_terms = _draw_support(generator, ell, m, b_count)
    metadata = {
        "mode": "uniform",
        "shape": [ell, m],
        "split": [a_count, b_count],
        "total_weight": a_count + b_count,
        "split_index": split_index,
        "template": None,
        "operations": [],
    }
    return _result(
        a_terms, b_terms, metadata, return_metadata=return_metadata,
    )


def _template_fits(template: FrontierTemplate, ell: int, m: int) -> bool:
    terms = template.a_terms + template.b_terms
    return (
        len(template.a_terms) >= 2
        and len(template.b_terms) >= 2
        and len(terms) <= 6
        and all(0 <= x < ell and 0 <= y < m for x, y in terms)
        and len(set(template.a_terms)) == len(template.a_terms)
        and len(set(template.b_terms)) == len(template.b_terms)
    )


def _units(modulus: int) -> tuple[int, ...]:
    return tuple(value for value in range(1, modulus) if gcd(value, modulus) == 1)


def _transform_support(
    terms: Sequence[Term],
    *,
    ell: int,
    m: int,
    unit_x: int,
    unit_y: int,
    shift_x: int,
    shift_y: int,
) -> Support:
    return sorted({
        (
            (unit_x * int(x) + shift_x) % ell,
            (unit_y * int(y) + shift_y) % m,
        )
        for x, y in terms
    })


def _mutate_one(
    rng: np.random.Generator,
    a_terms: Support,
    b_terms: Support,
    *,
    ell: int,
    m: int,
    radius: int,
) -> dict[str, Any] | None:
    """Apply one bounded, count-preserving edit, retrying collisions."""

    blocks = (a_terms, b_terms)
    for _ in range(64):
        block_index = int(rng.integers(2))
        block = blocks[block_index]
        term_index = int(rng.integers(len(block)))
        dx = int(rng.integers(-radius, radius + 1))
        dy = int(rng.integers(-radius, radius + 1))
        if dx == 0 and dy == 0:
            continue
        old = block[term_index]
        new = ((old[0] + dx) % ell, (old[1] + dy) % m)
        if new == old or new in block:
            continue
        block[term_index] = new
        block.sort()
        return {
            "op": "local-mutation",
            "block": "A" if block_index == 0 else "B",
            "from": list(old),
            "to": list(new),
            "delta": [dx, dy],
        }
    return None


def sample_structured_frontier(
    ell: int,
    m: int,
    *,
    rng: RngLike = None,
    templates: Sequence[FrontierTemplate] = FRONTIER_TEMPLATES,
    template_labels: Sequence[str] | None = None,
    max_mutations: int = 1,
    mutation_radius: int = 1,
    swap_probability: float = 0.5,
    return_metadata: bool = False,
) -> SupportPair | SampleWithMetadata:
    """Sample a bounded mutation of a compatible sparse frontier template.

    A template from a smaller lattice is eligible only when all of its
    exponents already fit the target shape.  Such cross-shape support reuse is
    recorded explicitly in metadata and is not described as an equivalence or
    lift.  On the target ring, unit coordinate scaling is an automorphism and
    monomial translation is multiplication by a unit.  Both are bijections on
    monomials and therefore preserve support size.
    """

    ell, m = _validate_shape(ell, m)
    if isinstance(max_mutations, bool) or int(max_mutations) != max_mutations:
        raise TypeError("max_mutations must be an integer")
    max_mutations = int(max_mutations)
    if max_mutations < 0:
        raise ValueError("max_mutations must be non-negative")
    if mutation_radius < 1:
        raise ValueError("mutation_radius must be at least one")
    if not 0.0 <= swap_probability <= 1.0:
        raise ValueError("swap_probability must lie in [0, 1]")

    selected_labels = set(template_labels) if template_labels is not None else None
    candidates = tuple(
        template
        for template in templates
        if (selected_labels is None or template.label in selected_labels)
        and _template_fits(template, ell, m)
    )
    if not candidates:
        requested = "all templates" if selected_labels is None else sorted(selected_labels)
        raise ValueError(
            f"no frontier template compatible with shape ({ell}, {m}) "
            f"and selection {requested}"
        )

    generator = _coerce_rng(rng)
    template_index = int(generator.integers(len(candidates)))
    template = candidates[template_index]
    unit_x_values, unit_y_values = _units(ell), _units(m)
    unit_x = unit_x_values[int(generator.integers(len(unit_x_values)))]
    unit_y = unit_y_values[int(generator.integers(len(unit_y_values)))]
    a_shift = (int(generator.integers(ell)), int(generator.integers(m)))
    b_shift = (int(generator.integers(ell)), int(generator.integers(m)))

    a_terms = _transform_support(
        template.a_terms,
        ell=ell,
        m=m,
        unit_x=unit_x,
        unit_y=unit_y,
        shift_x=a_shift[0],
        shift_y=a_shift[1],
    )
    b_terms = _transform_support(
        template.b_terms,
        ell=ell,
        m=m,
        unit_x=unit_x,
        unit_y=unit_y,
        shift_x=b_shift[0],
        shift_y=b_shift[1],
    )
    # Unit coordinate scaling and monomial translation are bijective, so a
    # compatible template cannot collapse. Keep this assertion close to the
    # transform because a future non-unit transform would violate the guarantee.
    if len(a_terms) != len(template.a_terms) or len(b_terms) != len(template.b_terms):
        raise AssertionError("target-ring automorphism unexpectedly collapsed support")

    operations: list[dict[str, Any]] = [
        {
            "op": "unit-scaling",
            "unit_x": unit_x,
            "unit_y": unit_y,
        },
        {
            "op": "translation",
            "A": list(a_shift),
            "B": list(b_shift),
        },
    ]
    swapped = bool(generator.random() < swap_probability)
    if swapped:
        a_terms, b_terms = b_terms, a_terms
        operations.append({"op": "exchange-A-B"})

    # At an exact template shape, the algebraic transformations alone mostly
    # explore an equivalence orbit. Make at least one local edit by default so
    # structured samples can leave that orbit; callers can request zero edits
    # explicitly with max_mutations=0.
    mutation_count = (
        int(generator.integers(1, max_mutations + 1)) if max_mutations else 0
    )
    completed_mutations = 0
    for _ in range(mutation_count):
        operation = _mutate_one(
            generator,
            a_terms,
            b_terms,
            ell=ell,
            m=m,
            radius=int(mutation_radius),
        )
        if operation is not None:
            operations.append(operation)
            completed_mutations += 1

    metadata = {
        "mode": "structured-frontier",
        "shape": [ell, m],
        "split": [len(a_terms), len(b_terms)],
        "total_weight": len(a_terms) + len(b_terms),
        "template": {
            "label": template.label,
            "shape": [template.ell, template.m],
            "split": [len(template.a_terms), len(template.b_terms)],
            "evidence": template.evidence,
            "shape_adaptation": (
                "exact" if (template.ell, template.m) == (ell, m)
                else "support-reuse"
            ),
        },
        "mutations_requested": mutation_count,
        "mutations_completed": completed_mutations,
        "swapped": swapped,
        "operations": operations,
    }
    return _result(
        a_terms, b_terms, metadata, return_metadata=return_metadata,
    )


def sample_mixed(
    ell: int,
    m: int,
    *,
    rng: RngLike = None,
    structured_probability: float = 0.7,
    uniform_splits: Sequence[tuple[int, int]] = DEFAULT_SPLITS,
    templates: Sequence[FrontierTemplate] = FRONTIER_TEMPLATES,
    template_labels: Sequence[str] | None = None,
    max_mutations: int = 1,
    mutation_radius: int = 1,
    swap_probability: float = 0.5,
    return_metadata: bool = False,
) -> SupportPair | SampleWithMetadata:
    """Mix uniform exploration with structured frontier exploitation."""

    if not 0.0 <= structured_probability <= 1.0:
        raise ValueError("structured_probability must lie in [0, 1]")
    generator = _coerce_rng(rng)
    use_structured = bool(generator.random() < structured_probability)
    if use_structured:
        a_terms, b_terms, component = sample_structured_frontier(
            ell,
            m,
            rng=generator,
            templates=templates,
            template_labels=template_labels,
            max_mutations=max_mutations,
            mutation_radius=mutation_radius,
            swap_probability=swap_probability,
            return_metadata=True,
        )
    else:
        a_terms, b_terms, component = sample_uniform(
            ell,
            m,
            rng=generator,
            splits=uniform_splits,
            return_metadata=True,
        )

    metadata = {
        **component,
        "mode": "mixed",
        "component_mode": component["mode"],
        "structured_probability": float(structured_probability),
    }
    return _result(
        a_terms, b_terms, metadata, return_metadata=return_metadata,
    )


def sample_bb_supports(
    mode: str,
    ell: int,
    m: int,
    **kwargs: Any,
) -> SupportPair | SampleWithMetadata:
    """Dispatch by a stable string mode for command-line/search integrations."""

    normalized = mode.strip().lower().replace("_", "-")
    if normalized == "uniform":
        return sample_uniform(ell, m, **kwargs)
    if normalized in {"structured", "structured-frontier", "frontier"}:
        return sample_structured_frontier(ell, m, **kwargs)
    if normalized == "mixed":
        return sample_mixed(ell, m, **kwargs)
    raise ValueError(
        "mode must be one of: uniform, structured-frontier, mixed"
    )


# Descriptive aliases for callers that prefer an explicit BB prefix.
sample_uniform_bb = sample_uniform
sample_structured_bb = sample_structured_frontier
sample_mixed_bb = sample_mixed


__all__ = [
    "DEFAULT_SPLITS",
    "FRONTIER_TEMPLATES",
    "FrontierTemplate",
    "sample_bb_supports",
    "sample_mixed",
    "sample_mixed_bb",
    "sample_structured_bb",
    "sample_structured_frontier",
    "sample_uniform",
    "sample_uniform_bb",
]
