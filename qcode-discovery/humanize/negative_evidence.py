"""Central replay gates for negative-only Stage-1 scheduling evidence.

These helpers may save an exact-audit slot, but they never grant positive
distance credit and are not part of the proof or final-acceptance gates.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any

import numpy as np

from evaluation.construction import build_css_code_from_claim
from evaluation.distance_milp import (
    get_code_matrices,
    replay_css_direction_witness,
    symplectic_weight_witness,
)
from evaluation.structural_dedup import (
    _validate_logical_basis_upper_bound_report,
)
from evaluation.target_policy import target_binding, validate_target_mode


@dataclass(frozen=True)
class StructuralLogicalBasisRejection:
    """A rebuilt logical operator that is strictly below the target."""

    target_mode: str
    n: int
    k: int
    upper_bound: int
    required_distance: int


def _reported_positive_int(value: Any) -> int | None:
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        return None
    return value


def _replay_operator_against_rebuilt_code(
    code: Any,
    witness: Mapping[str, Any],
) -> bool:
    """Bind the stored operator bits to rebuilt checks and logical rows."""

    try:
        hx, hz, lx, lz = get_code_matrices(code)
        side = witness["side"]
        index = witness["index"]
        dual_index = witness["dual_index"]
        weight = witness["weight"]
        bits = witness["bits"]
        if side == "X":
            rows, checks, duals = lx, hz, lz
        elif side == "Z":
            rows, checks, duals = lz, hx, lx
        else:
            return False
        if (
            isinstance(index, bool)
            or not isinstance(index, int)
            or index < 0
            or index >= rows.shape[0]
            or isinstance(dual_index, bool)
            or not isinstance(dual_index, int)
            or dual_index < 0
            or dual_index >= duals.shape[0]
        ):
            return False
        rebuilt_bits = [
            int(value)
            for value in np.asarray(rows[index], dtype=np.uint8).reshape(-1) % 2
        ]
        if rebuilt_bits != bits:
            return False
        replayed = replay_css_direction_witness(
            checks,
            duals[dual_index],
            weight,
            bits,
        )
        return replayed == bits
    except Exception:
        return False


def replay_structural_logical_basis_rejection(
    row: Mapping[str, Any],
    *,
    target_mode: str,
) -> StructuralLogicalBasisRejection | None:
    """Return a replayed target rejection, or keep the Stage-1 audit slot.

    The structural report's self-hash is only an input-integrity check.  This
    boundary independently rebuilds the CSS code from its construction,
    recomputes the minimum symplectic-basis witness, and verifies the stored
    operator against rebuilt checks and an opposite logical row.  Only
    ``upper_bound < required_distance`` authorizes a negative-only skip.

    Every absent, unsupported, malformed, mismatched, or non-rejecting claim
    returns ``None``.  In particular, legacy/twisted/compact construction
    shapes not understood by :func:`build_css_code_from_claim` remain in the
    expensive audit queue instead of being silently discarded.
    """

    try:
        mode = validate_target_mode(target_mode)
        static = row.get("static_eligibility")
        if (
            not isinstance(static, Mapping)
            or static.get("checked") is not True
            or static.get("eligible") is not True
        ):
            return None
        report = static.get("logical_basis_upper_bound")
        if not isinstance(report, Mapping):
            return None
        report = dict(report)
        _validate_logical_basis_upper_bound_report(report)
        if report.get("available") is not True:
            return None

        code = build_css_code_from_claim(row)
        rebuilt_n = int(code.num_qudits)
        rebuilt_k = int(code.dimension)
        row_n = _reported_positive_int(row.get("n"))
        row_k = _reported_positive_int(row.get("k"))
        static_n = _reported_positive_int(static.get("n"))
        static_k = _reported_positive_int(static.get("k"))
        if (
            row_n != rebuilt_n
            or row_k != rebuilt_k
            or static_n != rebuilt_n
            or static_k != rebuilt_k
        ):
            return None

        stored_witness = report.get("witness")
        fresh_witness = symplectic_weight_witness(code)
        if (
            not isinstance(stored_witness, Mapping)
            or not isinstance(fresh_witness, Mapping)
            or dict(stored_witness) != dict(fresh_witness)
            or report.get("upper_bound") != fresh_witness.get("weight")
            or not _replay_operator_against_rebuilt_code(
                code,
                stored_witness,
            )
        ):
            return None

        binding = target_binding(rebuilt_n, rebuilt_k, mode)
        required = _reported_positive_int(binding.get("required_distance"))
        upper_bound = _reported_positive_int(report.get("upper_bound"))
        if (
            required is None
            or upper_bound is None
            or upper_bound >= required
        ):
            return None
        return StructuralLogicalBasisRejection(
            target_mode=mode,
            n=rebuilt_n,
            k=rebuilt_k,
            upper_bound=upper_bound,
            required_distance=required,
        )
    except Exception:
        # Negative evidence is optional scheduling evidence.  Any replay
        # failure must preserve the candidate's exact-audit opportunity.
        return None


__all__ = [
    "StructuralLogicalBasisRejection",
    "replay_structural_logical_basis_rejection",
]
