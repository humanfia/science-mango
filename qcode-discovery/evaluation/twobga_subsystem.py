"""Strict single-block subsystem problems for two-block CSS BB codes.

Lin and Pryadko, Phys. Rev. A 109, 022407 (2024), Statement 5 proves

``d(H_X=[A|B], H_Z=[B^T|A^T]) >= d(CSS(A, B^T))``

only when both rank defects vanish.  This module reconstructs those defects
over GF(2), refuses vacuous subsystem instances, and builds the two quotient
problems whose simultaneous lower bounds define the subsystem distance.

The distinction is essential for multivariate bicycle codes.  An Abelian
matrix presentation does not justify silently assuming zero defects: some
valid BB matrices have ``k_S=0`` while all original logical qubits live in
the defect sectors.  Treating the empty auxiliary code as having infinite
distance would then create a false lower bound for the original code.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

import numpy as np


TWOBGA_SUBSYSTEM_METHOD = "lin-pryadko-statement-5-rank-defect-replay-v1"
TWOBGA_SUBSYSTEM_SCHEMA_VERSION = 1
TWOBGA_SUBSYSTEM_REFERENCE = {
    "doi": "10.1103/PhysRevA.109.022407",
    "statement": 5,
    "equation": 33,
}
try:
    _SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
except OSError:
    _SOURCE_SHA256 = None


def _canonical_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def matrix_sha256(matrix: np.ndarray) -> str:
    """Hash a binary matrix together with its exact dimensions."""

    value = np.ascontiguousarray(np.asarray(matrix, dtype=np.uint8) & 1)
    if value.ndim != 2:
        raise ValueError("matrix must be two-dimensional")
    digest = hashlib.sha256()
    digest.update(json.dumps(list(value.shape), separators=(",", ":")).encode())
    digest.update(b"\0")
    digest.update(value.tobytes(order="C"))
    return digest.hexdigest()


def gf2_rref(matrix: np.ndarray) -> tuple[np.ndarray, tuple[int, ...]]:
    """Return reduced row echelon form and pivots over GF(2)."""

    value = np.asarray(matrix, dtype=np.uint8).copy() & 1
    if value.ndim != 2:
        raise ValueError("GF(2) row reduction requires a matrix")
    rows, columns = value.shape
    pivot_row = 0
    pivots: list[int] = []
    for column in range(columns):
        candidates = np.flatnonzero(value[pivot_row:, column])
        if not len(candidates):
            continue
        selected = pivot_row + int(candidates[0])
        if selected != pivot_row:
            value[[pivot_row, selected]] = value[[selected, pivot_row]]
        other_rows = np.flatnonzero(value[:, column])
        other_rows = other_rows[other_rows != pivot_row]
        if len(other_rows):
            value[other_rows] ^= value[pivot_row]
        pivots.append(column)
        pivot_row += 1
        if pivot_row == rows:
            break
    return value, tuple(pivots)


def gf2_rank(matrix: np.ndarray) -> int:
    """Return exact binary rank; never use a real-valued rank surrogate."""

    return len(gf2_rref(matrix)[1])


def gf2_nullspace(matrix: np.ndarray) -> np.ndarray:
    """Return rows forming a basis of the right nullspace over GF(2)."""

    reduced, pivots = gf2_rref(matrix)
    columns = int(reduced.shape[1])
    pivot_set = set(pivots)
    free = [column for column in range(columns) if column not in pivot_set]
    basis = np.zeros((len(free), columns), dtype=np.uint8)
    for basis_row, free_column in enumerate(free):
        basis[basis_row, free_column] = 1
        for row, pivot in enumerate(pivots):
            basis[basis_row, pivot] = reduced[row, free_column]
    if basis.size and np.any((np.asarray(matrix, dtype=np.uint8) @ basis.T) & 1):
        raise RuntimeError("internal GF(2) nullspace construction failed")
    return basis


def _same_rowspace(left: np.ndarray, right: np.ndarray) -> bool:
    first = np.asarray(left, dtype=np.uint8) & 1
    second = np.asarray(right, dtype=np.uint8) & 1
    if first.ndim != 2 or second.ndim != 2 or first.shape[1] != second.shape[1]:
        return False
    left_rank = gf2_rank(first)
    right_rank = gf2_rank(second)
    return bool(
        left_rank == right_rank == gf2_rank(np.vstack((first, second)))
    )


def _translation_report(
    checks: np.ndarray,
    gauge: np.ndarray,
    *,
    ell: int,
    m: int,
    sector: str,
) -> dict[str, Any]:
    """Verify a transitive torus action for an optional one-coordinate anchor."""

    block = ell * m
    grid = np.arange(block, dtype=np.int64).reshape(ell, m)
    generators: list[dict[str, Any]] = []
    for axis, name, order in ((0, "x", ell), (1, "y", m)):
        permutation = np.roll(grid, 1, axis=axis).ravel()
        generators.append({
            "axis": name,
            "order": order,
            "checks_rowspace_preserved": _same_rowspace(
                checks, checks[:, permutation],
            ),
            "gauge_rowspace_preserved": _same_rowspace(
                gauge, gauge[:, permutation],
            ),
            "permutation_sha256": hashlib.sha256(
                np.asarray(permutation, dtype="<u4").tobytes(),
            ).hexdigest(),
        })
    report: dict[str, Any] = {
        "method": "twobga-subsystem-torus-rowspace-v1",
        "sector": sector,
        "shape": [ell, m],
        "block_size": block,
        "verified": bool(
            ell > 0
            and m > 0
            and checks.shape[1] == gauge.shape[1] == block
            and all(
                item["checks_rowspace_preserved"]
                and item["gauge_rowspace_preserved"]
                for item in generators
            )
        ),
        "orbit_representatives": [0],
        "orbit_sizes": [block],
        "generators": generators,
    }
    report["report_sha256"] = _canonical_sha256(report)
    return report


@dataclass(frozen=True)
class TwoBgaSubsystemProblem:
    """Matrices plus a replayable eligibility report for Statement 5."""

    a: np.ndarray
    b: np.ndarray
    x_checks: np.ndarray
    x_detectors: np.ndarray
    x_gauge: np.ndarray
    z_checks: np.ndarray
    z_detectors: np.ndarray
    z_gauge: np.ndarray
    report: dict[str, Any]

    @property
    def eligible(self) -> bool:
        return self.report.get("eligible") is True

    def sector_matrices(
        self, sector: str,
    ) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        normalized = str(sector).upper()
        if normalized == "X":
            return self.x_checks, self.x_detectors, self.x_gauge
        if normalized == "Z":
            return self.z_checks, self.z_detectors, self.z_gauge
        raise ValueError("subsystem sector must be X or Z")


def derive_twobga_subsystem_problem(
    hx: np.ndarray,
    hz: np.ndarray,
    *,
    ell: int,
    m: int,
    expected_n: int | None = None,
    expected_k: int | None = None,
) -> TwoBgaSubsystemProblem:
    """Rebuild ``CSS(A,B^T)`` and prove whether Statement 5 is applicable.

    For ``G_X=A`` and ``G_Z=B^T`` we first reconstruct the centers

    ``S_X = row(G_X) intersect row(G_Z)^perp`` and
    ``S_Z = row(G_Z) intersect row(G_X)^perp``.

    The two dressed protected quotient predicates are

    * Z: ``S_X z = 0`` and ``z not in row(B^T)``;
    * X: ``S_Z x = 0`` and ``x not in row(A)``.

    A basis of ``ker(G)`` detects non-membership in ``row(G)`` exactly.  We
    restrict those functionals to the applicable stabilizer kernel and retain
    a deterministic independent basis (exactly ``k_S`` rows for an eligible
    instance).  Both directions must be audited; the original BB X/Z
    isometry is not silently transferred to this subsystem code.
    """

    if _SOURCE_SHA256 is None:
        raise RuntimeError("cannot fingerprint twobga_subsystem.py")
    ell_value = int(ell)
    m_value = int(m)
    if ell_value <= 0 or m_value <= 0:
        raise ValueError("ell and m must be positive")
    block = ell_value * m_value
    matrix_x = np.asarray(hx, dtype=np.uint8) & 1
    matrix_z = np.asarray(hz, dtype=np.uint8) & 1
    if matrix_x.ndim != 2 or matrix_z.ndim != 2:
        raise ValueError("H_X and H_Z must be matrices")
    if matrix_x.shape != (block, 2 * block):
        raise ValueError("H_X is not a square-block BB matrix")
    if matrix_z.shape != (block, 2 * block):
        raise ValueError("H_Z is not a square-block BB matrix")

    a = np.ascontiguousarray(matrix_x[:, :block])
    b = np.ascontiguousarray(matrix_x[:, block:])
    product_ab = (a @ b) & 1
    product_ba = (b @ a) & 1
    standard_form = bool(
        np.array_equal(matrix_z[:, :block], b.T)
        and np.array_equal(matrix_z[:, block:], a.T)
    )
    commuting_blocks = bool(np.array_equal(product_ab, product_ba))
    css_commutation = not bool(np.any((matrix_x @ matrix_z.T) & 1))

    rank_a = gf2_rank(a)
    rank_b = gf2_rank(b)
    rank_ab = gf2_rank(product_ab)
    rank_hx = gf2_rank(matrix_x)
    rank_hz = gf2_rank(matrix_z)
    original_k = 2 * block - rank_hx - rank_hz
    subsystem_k = block - rank_a - rank_b + rank_ab
    delta_x = block - subsystem_k - rank_hx
    delta_z = block - subsystem_k - rank_hz
    dimension_identity = bool(
        original_k == 2 * subsystem_k + delta_x + delta_z
    )

    def row_basis(matrix: np.ndarray) -> np.ndarray:
        reduced, pivots = gf2_rref(matrix)
        return np.ascontiguousarray(reduced[: len(pivots)])

    def center_basis(
        gauge: np.ndarray,
        opposite_gauge: np.ndarray,
    ) -> np.ndarray:
        independent_gauge = row_basis(gauge)
        coefficients = gf2_nullspace(
            (opposite_gauge @ independent_gauge.T) & 1,
        )
        return row_basis((coefficients @ independent_gauge) & 1)

    def restricted_detectors(
        checks: np.ndarray,
        gauge: np.ndarray,
    ) -> tuple[np.ndarray, np.ndarray]:
        full = gf2_nullspace(gauge)
        combined = row_basis(checks)
        current_rank = int(combined.shape[0])
        selected: list[np.ndarray] = []
        for row in full:
            trial = np.vstack((combined, row))
            trial_rank = gf2_rank(trial)
            if trial_rank == current_rank:
                continue
            selected.append(row.copy())
            combined = row_basis(trial)
            current_rank = trial_rank
        compressed = (
            np.vstack(selected).astype(np.uint8, copy=False)
            if selected else np.zeros((0, block), dtype=np.uint8)
        )
        return full, np.ascontiguousarray(compressed)

    x_gauge = a
    z_gauge = np.ascontiguousarray(b.T)
    # A dressed Z logical commutes with the X center; a dressed X logical
    # commutes with the Z center.  Using the full gauge matrices as checks
    # computes a bare distance and can overestimate the correctable subsystem
    # distance, so it is deliberately forbidden here.
    z_checks = center_basis(x_gauge, z_gauge)
    x_checks = center_basis(z_gauge, x_gauge)
    z_full_detectors, z_detectors = restricted_detectors(z_checks, z_gauge)
    x_full_detectors, x_detectors = restricted_detectors(x_checks, x_gauge)

    def detector_report(
        detectors: np.ndarray,
        full_detectors: np.ndarray,
        gauge: np.ndarray,
        checks: np.ndarray,
    ) -> dict[str, Any]:
        gauge_rank = gf2_rank(gauge)
        detector_rank = gf2_rank(detectors)
        checks_rank = gf2_rank(checks)
        checks_commute_with_gauge = not bool(
            np.any((gauge @ checks.T) & 1),
        )
        restricted_rank = gf2_rank(np.vstack((checks, detectors))) - checks_rank
        full_restricted_rank = (
            gf2_rank(np.vstack((checks, full_detectors))) - checks_rank
        )
        return {
            "verified": bool(
                gf2_rank(full_detectors) == block - gauge_rank
                and not np.any((gauge @ full_detectors.T) & 1)
                and checks_commute_with_gauge
                and detector_rank == subsystem_k
                and restricted_rank == full_restricted_rank == subsystem_k
            ),
            "distance_semantics": "dressed-logical-center-quotient",
            "check_rank": checks_rank,
            "checks_commute_with_gauge": checks_commute_with_gauge,
            "gauge_rank": gauge_rank,
            "detector_rank": detector_rank,
            "full_detector_rank": gf2_rank(full_detectors),
            "restricted_detector_rank": restricted_rank,
            "expected_restricted_detector_rank": subsystem_k,
            "checks_sha256": matrix_sha256(checks),
            "gauge_sha256": matrix_sha256(gauge),
            "detectors_sha256": matrix_sha256(detectors),
            "full_detectors_sha256": matrix_sha256(full_detectors),
        }

    x_detector_report = detector_report(
        x_detectors, x_full_detectors, x_gauge, x_checks,
    )
    z_detector_report = detector_report(
        z_detectors, z_full_detectors, z_gauge, z_checks,
    )
    x_translation = _translation_report(
        x_checks, x_gauge, ell=ell_value, m=m_value, sector="X",
    )
    z_translation = _translation_report(
        z_checks, z_gauge, ell=ell_value, m=m_value, sector="Z",
    )
    geometry_matches = bool(
        (expected_n is None or expected_n == 2 * block)
        and (expected_k is None or expected_k == original_k)
    )
    eligibility_checks = {
        "standard_bb_block_form": standard_form,
        "commuting_blocks": commuting_blocks,
        "css_commutation": css_commutation,
        "geometry_matches": geometry_matches,
        "dimension_identity": dimension_identity,
        "original_dimension_is_twice_subsystem": (
            original_k == 2 * subsystem_k
        ),
        "nonnegative_rank_defects": delta_x >= 0 and delta_z >= 0,
        "positive_subsystem_dimension": subsystem_k > 0,
        "zero_rank_defects": delta_x == 0 and delta_z == 0,
        "x_quotient_detector_verified": x_detector_report["verified"],
        "z_quotient_detector_verified": z_detector_report["verified"],
    }
    report: dict[str, Any] = {
        "schema_version": TWOBGA_SUBSYSTEM_SCHEMA_VERSION,
        "method": TWOBGA_SUBSYSTEM_METHOD,
        "source_sha256": _SOURCE_SHA256,
        "reference": dict(TWOBGA_SUBSYSTEM_REFERENCE),
        "eligible": all(eligibility_checks.values()),
        "eligibility_checks": eligibility_checks,
        "shape": [ell_value, m_value],
        "original_n": 2 * block,
        "original_k": original_k,
        "subsystem_n": block,
        "subsystem_k": subsystem_k,
        "rank_defects": {"delta_x": delta_x, "delta_z": delta_z},
        "ranks": {
            "A": rank_a,
            "B": rank_b,
            "AB": rank_ab,
            "H_X": rank_hx,
            "H_Z": rank_hz,
        },
        "matrix_sha256": {
            "H_X": matrix_sha256(matrix_x),
            "H_Z": matrix_sha256(matrix_z),
            "A": matrix_sha256(a),
            "B": matrix_sha256(b),
            "AB": matrix_sha256(product_ab),
        },
        "sectors": {
            "X": {
                **x_detector_report,
                "predicate": "S_Z x = 0 and x not in row(A)",
                "translation_symmetry": x_translation,
            },
            "Z": {
                **z_detector_report,
                "predicate": "S_X z = 0 and z not in row(B^T)",
                "translation_symmetry": z_translation,
            },
        },
        "lower_bound_semantics": {
            "required_sectors": ["X", "Z"],
            "promotion": "both auxiliary sectors UNSAT through d-1",
            "auxiliary_sat_witness": "inconclusive-for-original-code",
        },
    }
    report["report_sha256"] = _canonical_sha256(report)
    return TwoBgaSubsystemProblem(
        a=a,
        b=b,
        x_checks=x_checks,
        x_detectors=x_detectors,
        x_gauge=x_gauge,
        z_checks=z_checks,
        z_detectors=z_detectors,
        z_gauge=z_gauge,
        report=report,
    )


def report_matches_problem(
    stored: Mapping[str, Any],
    problem: TwoBgaSubsystemProblem,
) -> bool:
    """Return whether a stored theorem report exactly replays."""

    return bool(dict(stored) == problem.report)


__all__ = [
    "TWOBGA_SUBSYSTEM_METHOD",
    "TWOBGA_SUBSYSTEM_REFERENCE",
    "TWOBGA_SUBSYSTEM_SCHEMA_VERSION",
    "TwoBgaSubsystemProblem",
    "derive_twobga_subsystem_problem",
    "gf2_nullspace",
    "gf2_rank",
    "gf2_rref",
    "matrix_sha256",
    "report_matches_problem",
]
