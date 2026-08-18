#!/usr/bin/env python3
"""Screen one CSS BB candidate with exact, disjoint SAT proof units."""

from __future__ import annotations

import hashlib
import json
import math
import os
import threading
import time
import uuid
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from pathlib import Path
from typing import Any, Mapping

import numpy as np

from evaluation.bb_sector_isometry import verify_bb_xz_sector_isometry
from evaluation.css_logical_detector import verify_css_logical_detectors
from evaluation.distance_milp import get_code_matrices
from evaluation.distance_distqldpc import (
    DEFAULT_DISTQLDPC_EXE,
    DISTQLDPC_CARDINALITY_MODES,
    DISTQLDPC_EVIDENCE_KIND,
    DISTQLDPC_TERMINAL_OUTCOMES,
    solve_css_distance_distqldpc_lower,
    verify_distqldpc_exact_evidence,
    verify_distqldpc_lower_evidence,
)
from evaluation.geometry import candidate_geometry
from evaluation.distance_sat import (
    SAT_AUTO_SOLVERS,
    SAT_EVIDENCE_KIND,
    SAT_EVIDENCE_SCHEMA_VERSION,
    SAT_INCREMENTAL_POLICY,
    SAT_INCREMENTAL_SOLVERS,
    SAT_TERMINAL_OUTCOMES,
    solve_css_sector_sat,
    verify_css_threshold_sat_witness,
)
from scripts.screen_frontier_candidate import (
    build_candidate_code,
    validate_candidate_parameters,
)
from scripts.screen_frontier_xor import verify_bb_translation_symmetry


SAT_STAGE3_GATE = "qldpc-frontier-sat-sector-exact-screen"
SAT_STAGE3_SCHEMA_VERSION = 1
SAT_COVERAGE_MODES = frozenset({"global", "first-nonzero"})
SAT_LOWER_BACKENDS = frozenset({"pysat", "distqldpc"})
DEFAULT_SAT_LOWER_BACKEND = "pysat"
DISTQLDPC_PHASE_PREFIX = "lower-distqldpc-"
SAT_PORTFOLIO_POLICY_V1 = "lower-fair-solver-encoding-portfolio-v1"
SAT_PORTFOLIO_POLICY = "lower-fair-diversity-first-portfolio-v2"
SAT_COMPATIBLE_PORTFOLIO_POLICIES = frozenset({
    SAT_PORTFOLIO_POLICY_V1,
    SAT_PORTFOLIO_POLICY,
})
SAT_DIVERSITY_WARMUP_WIDTH = 4
SAT_CANDIDATE_DEADLINE_SLACK_S = 5.0
SAT_ATTEMPT_SCHEMA_VERSION = 1
SAT_ONE_SHOT_POLICY = "one-shot-spawn-v1"
SAT_EXECUTION_POLICIES = frozenset({
    SAT_ONE_SHOT_POLICY,
    SAT_INCREMENTAL_POLICY,
})
SAT_ANCHOR_CUBE_SCHEMA_VERSION = 1
GENERIC_SYMMETRY_SCHEMA_VERSION = 1
GENERIC_SYMMETRY_GATE = "qldpc-generic-css-construction-symmetry-replay"


def _canonical_sha256(value: Any, *, omit: str | None = None) -> str:
    payload = dict(value) if isinstance(value, Mapping) else value
    if omit is not None and isinstance(payload, dict):
        payload.pop(omit, None)
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(
        f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp",
    )
    try:
        with temporary.open("w", encoding="utf-8") as stream:
            json.dump(value, stream, indent=2, sort_keys=True, allow_nan=False)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
        try:
            descriptor = os.open(path.parent, os.O_RDONLY)
        except OSError:
            return
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    finally:
        temporary.unlink(missing_ok=True)


def _sector_matrices(
    sector: str,
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    if sector == "Z":
        return hx, lx, hz
    if sector == "X":
        return hz, lz, hx
    raise ValueError("sector must be X or Z")


def _validated_permutation(value: Any, size: int, *, name: str) -> np.ndarray:
    try:
        permutation = np.asarray(value, dtype=int).reshape(-1)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ValueError(f"{name} is not an integer permutation") from exc
    if (
        len(permutation) != size
        or sorted(permutation.tolist()) != list(range(size))
    ):
        raise ValueError(f"{name} is not a permutation of range({size})")
    return permutation


def _source_to_destination_permutation(
    value: Any,
    size: int,
    *,
    convention: str,
    name: str,
) -> np.ndarray:
    permutation = _validated_permutation(value, size, name=name)
    normalized = convention.strip().lower().replace("-", "_")
    if normalized in {
        "source_to_destination",
        "src_to_dst",
        "destination_index_for_source",
    }:
        return permutation
    if normalized in {
        "destination_to_source",
        "dst_to_src",
        "source_index_at_destination",
    }:
        return np.argsort(permutation)
    raise ValueError(f"unsupported permutation convention: {convention!r}")


def _derive_row_permutation(
    matrix: np.ndarray,
    qubit_permutation: np.ndarray,
) -> np.ndarray:
    """Derive source->destination check rows for a qubit automorphism."""

    checks = np.asarray(matrix, dtype=np.uint8) & 1
    inverse_qubits = np.argsort(qubit_permutation)
    buckets: dict[bytes, deque[int]] = {}
    for destination, row in enumerate(checks):
        buckets.setdefault(row.tobytes(), deque()).append(destination)
    row_permutation = np.empty(checks.shape[0], dtype=int)
    for source, row in enumerate(checks):
        transformed = np.ascontiguousarray(row[inverse_qubits]).tobytes()
        destinations = buckets.get(transformed)
        if not destinations:
            raise ValueError("qubit action does not preserve the check-row multiset")
        row_permutation[source] = destinations.popleft()
    if any(destinations for destinations in buckets.values()):
        raise ValueError("check-row relabeling is incomplete")
    return row_permutation


def _verify_matrix_automorphism(
    matrix: np.ndarray,
    qubit_permutation: np.ndarray,
    proposed_rows: Any,
    *,
    convention: str,
    name: str,
) -> tuple[np.ndarray, str]:
    checks = np.asarray(matrix, dtype=np.uint8) & 1
    rows = (
        _derive_row_permutation(checks, qubit_permutation)
        if proposed_rows is None
        else _source_to_destination_permutation(
            proposed_rows,
            checks.shape[0],
            convention=convention,
            name=name,
        )
    )
    replay = np.zeros_like(checks)
    replay[np.ix_(rows, qubit_permutation)] = checks
    if not np.array_equal(replay, checks):
        raise ValueError(f"{name} does not replay the check matrix")
    return rows, _canonical_sha256({
        "shape": list(checks.shape),
        "rows": rows.tolist(),
        "qubits": qubit_permutation.tolist(),
    })


def verify_construction_symmetry(
    candidate: Mapping[str, Any],
    hx: np.ndarray,
    hz: np.ndarray,
) -> dict[str, Any]:
    """Replay adapter-proposed CSS automorphisms and derive orbit anchors."""

    from evaluation.construction import (
        candidate_symmetry_generators,
        construction_identity,
        construction_source_fingerprint,
    )

    proposals_value = candidate_symmetry_generators(dict(candidate))
    default_convention = "source_to_destination"
    if isinstance(proposals_value, Mapping):
        default_convention = str(
            proposals_value.get("permutation_convention", default_convention)
        )
        proposals = proposals_value.get("generators")
    else:
        proposals = proposals_value
    if not isinstance(proposals, (list, tuple)):
        raise ValueError("construction symmetry proposals must be a list")
    n = int(hx.shape[1])
    if hz.shape[1] != n:
        raise ValueError("CSS matrix widths differ")
    accepted: list[dict[str, Any]] = []
    rejected: list[dict[str, Any]] = []
    qubit_generators: list[np.ndarray] = []
    for position, raw in enumerate(proposals):
        identifier = (
            str(raw.get("id"))
            if isinstance(raw, Mapping) and raw.get("id") is not None
            else f"generator-{position}"
        )
        try:
            if not isinstance(raw, Mapping):
                raise TypeError("proposal is not an object")
            convention = str(
                raw.get("permutation_convention", default_convention)
            )
            qubits = _source_to_destination_permutation(
                raw.get("qubit_permutation"),
                n,
                convention=convention,
                name="qubit_permutation",
            )
            x_rows, x_replay = _verify_matrix_automorphism(
                hx,
                qubits,
                raw.get("x_check_permutation"),
                convention=convention,
                name="x_check_permutation",
            )
            z_rows, z_replay = _verify_matrix_automorphism(
                hz,
                qubits,
                raw.get("z_check_permutation"),
                convention=convention,
                name="z_check_permutation",
            )
        except (KeyError, TypeError, ValueError, OverflowError) as exc:
            rejected.append({"id": identifier, "reason": str(exc)})
            continue
        qubit_generators.append(qubits)
        accepted.append({
            "id": identifier,
            "permutation_convention": "source_to_destination",
            "qubit_permutation": qubits.tolist(),
            "x_check_permutation": x_rows.tolist(),
            "z_check_permutation": z_rows.tolist(),
            "x_matrix_replay_sha256": x_replay,
            "z_matrix_replay_sha256": z_replay,
        })

    parent = list(range(n))

    def find(value: int) -> int:
        while parent[value] != value:
            parent[value] = parent[parent[value]]
            value = parent[value]
        return value

    def union(left: int, right: int) -> None:
        left_root, right_root = find(left), find(right)
        if left_root != right_root:
            parent[right_root] = left_root

    for generator in qubit_generators:
        for source, destination in enumerate(generator.tolist()):
            union(source, int(destination))
    orbits: dict[int, list[int]] = {}
    for qubit in range(n):
        orbits.setdefault(find(qubit), []).append(qubit)
    canonical_orbits = sorted(
        (sorted(orbit) for orbit in orbits.values()),
        key=lambda orbit: orbit[0],
    )
    nontrivial = any(
        any(source != destination for source, destination in enumerate(generator))
        for generator in qubit_generators
    )
    report: dict[str, Any] = {
        "schema_version": GENERIC_SYMMETRY_SCHEMA_VERSION,
        "gate": GENERIC_SYMMETRY_GATE,
        "verified": bool(accepted and nontrivial),
        "construction_identity": construction_identity(dict(candidate)),
        "construction_source_fingerprint": construction_source_fingerprint(),
        "matrix_sha256": {
            "hx": _canonical_sha256(pack_matrix_for_symmetry(hx)),
            "hz": _canonical_sha256(pack_matrix_for_symmetry(hz)),
        },
        "proposed_generators": len(proposals),
        "verified_generators": accepted,
        "rejected_generators": rejected,
        "orbits": canonical_orbits,
        "orbit_representatives": [orbit[0] for orbit in canonical_orbits],
        "orbits_cover_all_qubits": sorted(
            qubit for orbit in canonical_orbits for qubit in orbit
        ) == list(range(n)),
        "coverage_theorem": (
            "verified automorphisms map any occupied qubit to the listed "
            "representative of its complete qubit orbit"
        ),
    }
    report["report_sha256"] = _canonical_sha256(report)
    return report


def pack_matrix_for_symmetry(matrix: np.ndarray) -> dict[str, Any]:
    binary = np.asarray(matrix, dtype=np.uint8) & 1
    return {
        "shape": list(binary.shape),
        "packed_hex": np.packbits(
            binary, axis=None, bitorder="little"
        ).tobytes().hex(),
    }


def _evidence_hash_valid(evidence: Mapping[str, Any]) -> bool:
    try:
        return evidence.get("evidence_sha256") == _canonical_sha256(
            evidence,
            omit="evidence_sha256",
        )
    except (TypeError, ValueError):
        return False


def _complete_unsat(evidence: Mapping[str, Any], threshold: int) -> bool:
    return bool(
        evidence.get("schema_version") == SAT_EVIDENCE_SCHEMA_VERSION
        and evidence.get("evidence_kind") == SAT_EVIDENCE_KIND
        and evidence.get("outcome") == "unsat"
        and evidence.get("decision_complete") is True
        and evidence.get("threshold_infeasible") is True
        and evidence.get("max_weight") == threshold
        and evidence.get("operator") is None
        and evidence.get("objective") is None
        and _evidence_hash_valid(evidence)
    )


def _anchor_cube_valid(
    cube: Mapping[str, Any],
    anchor_indices: tuple[int, ...],
) -> bool:
    try:
        cube_index = int(cube["cube_index"])
        expected = {
            "schema_version": SAT_ANCHOR_CUBE_SCHEMA_VERSION,
            "cover": "anchor-or-first-nonzero-v1",
            "cube_index": cube_index,
            "zero_anchor_indices": list(anchor_indices[:cube_index]),
            "one_anchor_index": anchor_indices[cube_index],
            "anchor_indices": list(anchor_indices),
        }
        expected["cube_sha256"] = _canonical_sha256(expected)
    except (IndexError, KeyError, TypeError, ValueError):
        return False
    return dict(cube) == expected


def _evidence_matches_anchor_cube(
    evidence: Mapping[str, Any],
    cube: Mapping[str, Any] | None,
) -> bool:
    """Fail closed unless evidence and its instance bind the same cube."""

    instance = evidence.get("instance")
    if cube is None:
        instance_cube_free = bool(
            not isinstance(instance, Mapping)
            or (
                instance.get("zero_anchor_indices", []) == []
                and instance.get("one_anchor_index") is None
                and instance.get("anchor_cube_sha256") is None
                and instance.get("anchor_unit_clauses") is None
                and instance.get("anchor_unit_clauses_sha256") is None
            )
        )
        return bool(
            evidence.get("zero_anchor_indices", []) == []
            and evidence.get("one_anchor_index") is None
            and evidence.get("anchor_cube_sha256") is None
            and instance_cube_free
        )
    zero_anchors = list(cube["zero_anchor_indices"])
    one_anchor = int(cube["one_anchor_index"])
    cube_sha256 = str(cube["cube_sha256"])
    clauses = [[-(int(index) + 1)] for index in zero_anchors]
    clauses.append([one_anchor + 1])
    cnf = evidence.get("cnf")
    cnf_binding_valid = bool(
        isinstance(cnf, Mapping)
        and cnf.get("anchor_unit_clauses_sha256")
        == _canonical_sha256(clauses)
    )
    # A hard timeout has no terminal CNF decision to promote and older solver
    # evidence omitted the redundant CNF summary.  Its fully self-hashed
    # instance is still safe scheduler history.  SAT/UNSAT terminal evidence
    # remains fail-closed unless the CNF binding is present.
    nonterminal_instance_only = bool(
        cnf is None
        and evidence.get("outcome") in {"hard_timeout", "cancelled"}
        and evidence.get("decision_complete") is False
    )
    binding_hash_valid = False
    if isinstance(instance, Mapping):
        unsigned_instance = dict(instance)
        binding_sha256 = unsigned_instance.pop("binding_sha256", None)
        try:
            binding_hash_valid = binding_sha256 == _canonical_sha256(
                unsigned_instance,
            )
        except (TypeError, ValueError):
            binding_hash_valid = False
    return bool(
        evidence.get("zero_anchor_indices") == zero_anchors
        and evidence.get("one_anchor_index") == one_anchor
        and evidence.get("anchor_cube_sha256") == cube_sha256
        and isinstance(instance, Mapping)
        and binding_hash_valid
        and instance.get("anchor_constraint_formulation")
        == "anchor-or-first-nonzero-unit-clauses-v1"
        and instance.get("anchor_indices") == cube["anchor_indices"]
        and instance.get("zero_anchor_indices") == zero_anchors
        and instance.get("one_anchor_index") == one_anchor
        and instance.get("anchor_cube_sha256") == cube_sha256
        and instance.get("anchor_unit_clauses") == clauses
        and instance.get("anchor_unit_clauses_sha256")
        == _canonical_sha256(clauses)
        and (cnf_binding_valid or nonterminal_instance_only)
    )


def _unit_key(
    phase: str,
    sector: str,
    partition: int | None,
    anchor_cube: Mapping[str, Any] | None = None,
) -> str:
    suffix = "global" if partition is None else f"p{partition:03d}"
    if anchor_cube is not None:
        cube_index = int(anchor_cube["cube_index"])
        cube_sha256 = str(anchor_cube["cube_sha256"])
        suffix += f"-c{cube_index:03d}-{cube_sha256[:12]}"
    return f"{phase}-{sector}-{suffix}"


def _distqldpc_phase(cardinality_mode: str) -> str:
    if cardinality_mode not in DISTQLDPC_CARDINALITY_MODES:
        raise ValueError("unsupported DistQLDPC cardinality mode")
    return f"{DISTQLDPC_PHASE_PREFIX}{cardinality_mode}"


def _distqldpc_mode_from_phase(phase: Any) -> str | None:
    if not isinstance(phase, str) or not phase.startswith(DISTQLDPC_PHASE_PREFIX):
        return None
    mode = phase[len(DISTQLDPC_PHASE_PREFIX):]
    return mode if mode in DISTQLDPC_CARDINALITY_MODES else None


def distqldpc_stage3_checkpoint_identity(
    candidate: Mapping[str, Any],
    *,
    cardinality_mode: str,
    coverage_mode: str,
    logical_detector: Mapping[str, Any],
    translation_symmetry: Mapping[str, Any] | None,
    construction_symmetry: Mapping[str, Any] | None,
    xz_sector_isometry: Mapping[str, Any] | None,
) -> dict[str, Any]:
    """Bind one external global-lower lane to this exact Stage-3 request."""

    if cardinality_mode not in DISTQLDPC_CARDINALITY_MODES:
        raise ValueError("unsupported DistQLDPC cardinality mode")
    if coverage_mode not in SAT_COVERAGE_MODES:
        raise ValueError("unsupported Stage-3 coverage mode")
    target = candidate.get("target")
    return {
        "stage3_gate": SAT_STAGE3_GATE,
        "candidate_digest": candidate["canonical_digest"],
        "target_mode": candidate.get("target_mode"),
        "target_binding_sha256": (
            target.get("binding_sha256") if isinstance(target, Mapping) else None
        ),
        "phase": "lower-distqldpc",
        "lower_backend": "distqldpc",
        "cardinality_mode": cardinality_mode,
        "coverage_mode": coverage_mode,
        "logical_detector_sha256": logical_detector["report_sha256"],
        "translation_symmetry": (
            None if translation_symmetry is None else dict(translation_symmetry)
        ),
        "construction_symmetry_sha256": (
            None
            if construction_symmetry is None
            else construction_symmetry.get("report_sha256")
        ),
        "xz_sector_isometry_sha256": (
            None
            if xz_sector_isometry is None
            else xz_sector_isometry.get("report_sha256")
        ),
    }


def _proof_plan(
    mode: str,
    k: int,
    sectors: tuple[str, ...] = ("X", "Z"),
    anchor_cover_cubes: list[Mapping[str, Any]] | None = None,
    lower_backend: str = DEFAULT_SAT_LOWER_BACKEND,
) -> list[tuple[str, str, int | None, int | None]]:
    if lower_backend not in SAT_LOWER_BACKENDS:
        raise ValueError("unsupported Stage-3 lower backend")
    partitions: tuple[int | None, ...] = (
        (None,) if mode == "global" else tuple(range(k))
    )
    # Lower-bound decisions decide rejection/progress directly.  Interleave
    # X/Z at each logical partition so a worker shortage cannot starve one
    # sector behind all k cases of the other.
    cube_indices: tuple[int | None, ...] = (
        tuple(range(len(anchor_cover_cubes)))
        if anchor_cover_cubes is not None
        else (None,)
    )
    lower = [
        ("lower", sector, partition, cube_index)
        for partition in partitions
        for sector in sectors
        for cube_index in cube_indices
    ]
    # Keep one unsplit global lower lane per sector when the anchor OR has
    # genuinely been divided.  CDCL may benefit from sharing learned clauses
    # across all logical syndromes/cubes; either this lane or the complete
    # partition-by-cube cover can independently establish the same bound.
    global_lower = (
        [("lower-global", sector, None, None) for sector in sectors]
        if anchor_cover_cubes is not None and len(anchor_cover_cubes) > 1
        else []
    )
    # Try the exact upper witness at R at the same time.  A witness below R is
    # an immediately replayable rejection; a weight-R witness completes the
    # exact proof once every lower unit is UNSAT.
    upper = [("upper", sector, None, None) for sector in sectors]
    external = (
        [(_distqldpc_phase(cardinality_mode), "XZ", None, None)
         for cardinality_mode in DISTQLDPC_CARDINALITY_MODES]
        if lower_backend == "distqldpc"
        else []
    )
    return external + global_lower + lower + upper


def _artifact(
    candidate: Mapping[str, Any],
    *,
    mode: str,
    translation_symmetry: Mapping[str, Any] | None,
    construction_symmetry: Mapping[str, Any] | None = None,
    logical_detector: Mapping[str, Any],
    units: Mapping[str, Mapping[str, Any]],
    expected_units: int,
    started: float,
    termination: Mapping[str, Any] | None = None,
    xz_sector_isometry: Mapping[str, Any] | None = None,
    proof_sectors: tuple[str, ...] = ("X", "Z"),
    anchor_cover_cubes: list[Mapping[str, Any]] | None = None,
    lower_backend: str = DEFAULT_SAT_LOWER_BACKEND,
    hx: np.ndarray | None = None,
    hz: np.ndarray | None = None,
    lx: np.ndarray | None = None,
    lz: np.ndarray | None = None,
) -> dict[str, Any]:
    required = int(candidate["required_distance"])
    k = int(candidate["k"])
    if lower_backend not in SAT_LOWER_BACKENDS:
        raise ValueError("unsupported Stage-3 lower backend")
    if lower_backend == "distqldpc" and any(
        matrix is None for matrix in (hx, hz, lx, lz)
    ):
        raise ValueError(
            "DistQLDPC artifact replay requires all CSS matrices"
        )
    if proof_sectors not in {("X",), ("X", "Z")}:
        raise ValueError("proof_sectors must be canonical X or complete X/Z")
    if proof_sectors == ("X",) and not (
        isinstance(xz_sector_isometry, Mapping)
        and xz_sector_isometry.get("verified") is True
        and xz_sector_isometry.get("canonical_sector") == "X"
        and xz_sector_isometry.get("covered_sectors") == ["X", "Z"]
    ):
        raise ValueError("canonical-sector proof requires verified X/Z isometry")
    if proof_sectors == ("X", "Z") and xz_sector_isometry is not None:
        raise ValueError("two-sector fallback must not publish an isometry report")
    if translation_symmetry is not None and construction_symmetry is not None:
        raise ValueError("BB and compact-construction symmetry reports cannot mix")
    if construction_symmetry is not None:
        if not (
            construction_symmetry.get("gate") == GENERIC_SYMMETRY_GATE
            and construction_symmetry.get("verified") is True
            and construction_symmetry.get("orbits_cover_all_qubits") is True
            and construction_symmetry.get("report_sha256")
            == _canonical_sha256(
                construction_symmetry,
                omit="report_sha256",
            )
        ):
            raise ValueError("compact-construction symmetry report is invalid")
    requested_cubes = (
        None
        if anchor_cover_cubes is None
        else [dict(cube) for cube in anchor_cover_cubes]
    )
    if requested_cubes is not None:
        if not requested_cubes:
            raise ValueError("anchor_cover_cubes must be nonempty when enabled")
        anchors = tuple(int(index) for index in requested_cubes[0].get(
            "anchor_indices", [],
        ))
        if not anchors or any(
            not _anchor_cube_valid(cube, anchors)
            for cube in requested_cubes
        ) or [cube["cube_index"] for cube in requested_cubes] != list(
            range(len(anchors)),
        ):
            raise ValueError("anchor_cover_cubes is not a complete ordered cover")
        if construction_symmetry is not None and list(anchors) != list(
            construction_symmetry.get("orbit_representatives", [])
        ):
            raise ValueError(
                "anchor cover does not match verified construction orbits"
            )
    partitions: tuple[int | None, ...] = (
        (None,) if mode == "global" else tuple(range(k))
    )
    expected_lower_partitions = len(proof_sectors) * len(partitions)
    decisions_per_partition = (
        len(requested_cubes) if requested_cubes is not None else 1
    )
    expected_lower = expected_lower_partitions * decisions_per_partition
    lower: list[dict[str, Any]] = []
    global_lower: list[dict[str, Any]] = []
    completed_cube_keys: set[tuple[str, int | None, str | None]] = set()
    upper_unsat: list[dict[str, Any]] = []
    low_witnesses: list[dict[str, Any]] = []
    exact_witnesses: list[dict[str, Any]] = []
    distqldpc_exact: list[dict[str, Any]] = []
    terminal = 0
    retryable = 0
    for key in sorted(units):
        unit = dict(units[key])
        evidence = unit.get("solver_evidence")
        if not isinstance(evidence, Mapping):
            continue
        # A partial artifact is an operational index, not the terminal
        # checkpoint itself.  Do not count a resumed terminal decision until
        # solve_css_sector_sat has rebound/replayed its checkpoint this run.
        if unit.get("checkpoint_replay_pending") is True:
            continue
        if evidence.get("outcome") in (
            SAT_TERMINAL_OUTCOMES | DISTQLDPC_TERMINAL_OUTCOMES
        ):
            terminal += 1
        elif evidence.get("retryable") is True:
            retryable += 1
        phase = unit.get("phase")
        sector = unit.get("sector")
        partition = unit.get("partition_index")
        unit_cube = unit.get("anchor_cube")
        external_mode = _distqldpc_mode_from_phase(phase)
        if external_mode is not None:
            if not (
                lower_backend == "distqldpc"
                and sector == "XZ"
                and partition is None
                and unit_cube is None
            ):
                continue
            assert hx is not None and hz is not None
            assert lx is not None and lz is not None
            checkpoint_identity = distqldpc_stage3_checkpoint_identity(
                candidate,
                cardinality_mode=external_mode,
                coverage_mode=mode,
                logical_detector=logical_detector,
                translation_symmetry=translation_symmetry,
                construction_symmetry=construction_symmetry,
                xz_sector_isometry=xz_sector_isometry,
            )
            failures = verify_distqldpc_exact_evidence(
                evidence,
                hx,
                hz,
                lx,
                lz,
                max_weight=required - 1,
                cardinality_mode=external_mode,
                expected_checkpoint_identity=checkpoint_identity,
            )
            if not failures:
                distqldpc_exact.append({
                    "unit_id": key,
                    "sector": "XZ",
                    "partition_index": None,
                    "anchor_cube": None,
                    "cardinality_mode": external_mode,
                    "checkpoint_identity": checkpoint_identity,
                    "solver_evidence": dict(evidence),
                })
            continue
        if phase == "lower" and _complete_unsat(evidence, required - 1):
            cube_valid = False
            cube_hash: str | None = None
            if requested_cubes is None:
                cube_valid = unit_cube is None and _evidence_matches_anchor_cube(
                    evidence, None,
                )
            elif isinstance(unit_cube, Mapping) and dict(unit_cube) in requested_cubes:
                cube_valid = _evidence_matches_anchor_cube(evidence, unit_cube)
                cube_hash = str(unit_cube["cube_sha256"])
            cube_key = (str(sector), partition, cube_hash)
            if (
                cube_valid
                and sector in proof_sectors
                and partition in partitions
                and cube_key not in completed_cube_keys
            ):
                completed_cube_keys.add(cube_key)
                lower.append({
                    "sector": sector,
                    "partition_index": partition,
                    "anchor_cube": (
                        None if unit_cube is None else dict(unit_cube)
                    ),
                    "solver_evidence": dict(evidence),
                })
        if (
            phase == "lower-global"
            and partition is None
            and unit_cube is None
            and sector in proof_sectors
            and _evidence_matches_anchor_cube(evidence, None)
            and _complete_unsat(evidence, required - 1)
        ):
            global_lower.append({
                "sector": sector,
                "partition_index": None,
                "anchor_cube": None,
                "solver_evidence": dict(evidence),
            })
        if (
            phase == "upper"
            and unit_cube is None
            and _evidence_matches_anchor_cube(evidence, None)
            and _complete_unsat(evidence, required)
        ):
            upper_unsat.append({
                "sector": sector,
                "partition_index": None,
                "anchor_cube": None,
                "solver_evidence": dict(evidence),
            })
        sat_cube_valid = bool(
            (
                phase == "upper"
                and sector in proof_sectors
                and partition is None
                and unit_cube is None
                and _evidence_matches_anchor_cube(evidence, None)
            )
            or (
                phase == "lower-global"
                and sector in proof_sectors
                and partition is None
                and unit_cube is None
                and _evidence_matches_anchor_cube(evidence, None)
            )
            or (
                phase == "lower"
                and sector in proof_sectors
                and partition in partitions
                and requested_cubes is None
                and unit_cube is None
                and _evidence_matches_anchor_cube(evidence, None)
            )
            or (
                phase == "lower"
                and sector in proof_sectors
                and partition in partitions
                and requested_cubes is not None
                and isinstance(unit_cube, Mapping)
                and dict(unit_cube) in requested_cubes
                and _evidence_matches_anchor_cube(evidence, unit_cube)
            )
        )
        if evidence.get("outcome") == "sat" and sat_cube_valid:
            objective = evidence.get("objective")
            if isinstance(objective, int) and not isinstance(objective, bool):
                wrapper = {
                    "sector": sector,
                    "partition_index": partition,
                    "anchor_cube": (
                        None if unit_cube is None else dict(unit_cube)
                    ),
                    "solver_evidence": dict(evidence),
                }
                if objective < required:
                    low_witnesses.append(wrapper)
                elif phase == "upper" and objective == required:
                    exact_witnesses.append(wrapper)

    completed_partition_keys: set[tuple[str, int | None]] = set()
    expected_cube_hashes = (
        {str(cube["cube_sha256"]) for cube in requested_cubes}
        if requested_cubes is not None
        else {None}
    )
    for sector in proof_sectors:
        for partition in partitions:
            observed = {
                cube_hash
                for item_sector, item_partition, cube_hash in completed_cube_keys
                if item_sector == sector and item_partition == partition
            }
            if observed == expected_cube_hashes:
                completed_partition_keys.add((sector, partition))
    lower_complete = len(completed_partition_keys) == expected_lower_partitions
    global_lower_by_sector = {
        str(item["sector"]): item for item in global_lower
    }
    global_lower_complete = set(global_lower_by_sector) == set(proof_sectors)
    upper_unsat_by_sector = {
        str(item["sector"]): item for item in upper_unsat
    }
    upper_unsat_complete = set(upper_unsat_by_sector) == set(proof_sectors)
    exact_witness = exact_witnesses[0] if exact_witnesses else None
    external_distances = sorted({
        int(item["solver_evidence"]["exact_distance"])
        for item in distqldpc_exact
    })
    external_conflict_reasons: list[str] = []
    if len(external_distances) > 1:
        external_conflict_reasons.append(
            "validated DistQLDPC lanes report different exact distances"
        )
    upper_witness_weight = (
        exact_witness["solver_evidence"].get("objective")
        if exact_witness is not None
        else None
    )
    if (
        isinstance(upper_witness_weight, int)
        and not isinstance(upper_witness_weight, bool)
        and any(
            distance != upper_witness_weight
            for distance in external_distances
        )
    ):
        external_conflict_reasons.append(
            "DistQLDPC exact distance disagrees with replayed upper witness"
        )
    pysat_lower_complete = lower_complete or global_lower_complete
    if pysat_lower_complete and any(
        distance <= required - 1 for distance in external_distances
    ):
        external_conflict_reasons.append(
            "DistQLDPC exact distance contradicts completed PySAT lower proof"
        )
    if upper_unsat_complete and any(
        distance <= required for distance in external_distances
    ):
        external_conflict_reasons.append(
            "DistQLDPC exact distance contradicts completed PySAT upper UNSAT"
        )
    low_witness_weights = [
        int(item["solver_evidence"]["objective"])
        for item in low_witnesses
    ]
    if low_witness_weights and any(
        distance > min(low_witness_weights)
        for distance in external_distances
    ):
        external_conflict_reasons.append(
            "DistQLDPC exact distance exceeds a replayed lower-weight witness"
        )
    distqldpc_conflict = bool(external_conflict_reasons)
    distqldpc_lower: list[dict[str, Any]] = []
    if not distqldpc_conflict:
        assert hx is not None or lower_backend != "distqldpc"
        assert hz is not None or lower_backend != "distqldpc"
        assert lx is not None or lower_backend != "distqldpc"
        assert lz is not None or lower_backend != "distqldpc"
        for wrapper in distqldpc_exact:
            if not verify_distqldpc_lower_evidence(
                wrapper["solver_evidence"],
                hx,
                hz,
                lx,
                lz,
                max_weight=required - 1,
                cardinality_mode=wrapper["cardinality_mode"],
                expected_checkpoint_identity=wrapper["checkpoint_identity"],
            ):
                distqldpc_lower.append(wrapper)
    external_lower_complete = bool(distqldpc_lower)
    external_effective = (
        min(
            distqldpc_lower,
            key=lambda item: DISTQLDPC_CARDINALITY_MODES.index(
                item["cardinality_mode"]
            ),
        )
        if external_lower_complete
        else None
    )
    lower_route_complete = bool(
        external_lower_complete or lower_complete or global_lower_complete
    )
    if distqldpc_conflict:
        status = "UNRESOLVED"
    elif low_witnesses:
        status = "REJECTED"
    elif lower_route_complete and exact_witness is not None:
        status = "EXACT_PROVEN"
    elif lower_route_complete or upper_unsat_complete:
        status = "THRESHOLD_PROVEN"
    else:
        status = "UNRESOLVED"
    global_route_complete = bool(
        not distqldpc_conflict
        and (upper_unsat_complete
             or external_lower_complete
             or global_lower_complete)
    )
    effective_mode = "global" if global_route_complete else mode
    if distqldpc_conflict:
        effective_lower = []
        lower_bound_backend = "pysat"
    elif upper_unsat_complete:
        effective_lower = [
            upper_unsat_by_sector[sector] for sector in proof_sectors
        ]
        lower_bound_backend = "pysat"
    elif external_effective is not None:
        effective_lower = [external_effective]
        lower_bound_backend = "distqldpc"
    elif global_lower_complete:
        effective_lower = [
            global_lower_by_sector[sector] for sector in proof_sectors
        ]
        lower_bound_backend = "pysat"
    else:
        effective_lower = lower
        lower_bound_backend = "pysat"
    lower_bound_threshold = required if upper_unsat_complete else required - 1
    effective_expected_lower = (
        1
        if external_effective is not None and not upper_unsat_complete
        else (len(proof_sectors) if global_route_complete else expected_lower)
    )
    effective_expected_partitions = (
        1
        if external_effective is not None and not upper_unsat_complete
        else (
            len(proof_sectors) if global_route_complete else expected_lower_partitions
        )
    )
    effective_completed_partitions = (
        len(effective_lower)
        if global_route_complete
        else len(completed_partition_keys)
    )
    value: dict[str, Any] = {
        "schema_version": SAT_STAGE3_SCHEMA_VERSION,
        "gate": SAT_STAGE3_GATE,
        "status": status,
        "candidate": dict(candidate),
        "target_mode": candidate.get("target_mode"),
        "target": (
            dict(candidate["target"])
            if isinstance(candidate.get("target"), Mapping)
            else None
        ),
        "required_distance": required,
        "coverage_mode": effective_mode,
        "requested_coverage_mode": mode,
        "requested_lower_backend": lower_backend,
        "lower_bound_backend": lower_bound_backend,
        "anchor_cover_cubes": None if global_route_complete else requested_cubes,
        "requested_anchor_cover_cubes": requested_cubes,
        "lower_bound_threshold": lower_bound_threshold,
        "threshold_only": False,
        "translation_symmetry": (
            None
            if translation_symmetry is None
            else dict(translation_symmetry)
        ),
        "construction_symmetry": (
            None
            if construction_symmetry is None
            else dict(construction_symmetry)
        ),
        "logical_detector": dict(logical_detector),
        "xz_sector_isometry": (
            None if xz_sector_isometry is None else dict(xz_sector_isometry)
        ),
        "expected_units": expected_units,
        "attempted_units": len(units),
        "terminal_units": terminal,
        "retryable_units": retryable,
        "portfolio_policy": SAT_PORTFOLIO_POLICY,
        "portfolio_attempts": sum(
            len(unit.get("attempts", []))
            for unit in units.values()
            if isinstance(unit.get("attempts"), list)
        ),
        "expected_lower_decisions": effective_expected_lower,
        "completed_lower_decisions": len(effective_lower),
        "expected_lower_partitions": effective_expected_partitions,
        "completed_lower_partitions": effective_completed_partitions,
        "lower_bound_decisions": effective_lower,
        "distqldpc_exact_distances": external_distances,
        "distqldpc_exact_decisions": distqldpc_exact,
        "distqldpc_lower_decisions": distqldpc_lower,
        "distqldpc_conflict": distqldpc_conflict,
        "distqldpc_conflict_details": (
            None
            if not distqldpc_conflict
            else {
                "reasons": external_conflict_reasons,
                "exact_distances": external_distances,
                "upper_witness_weight": upper_witness_weight,
            }
        ),
        "stage3_requested_lower_decisions": lower,
        "global_lower_decisions": global_lower,
        "upper_unsat_decisions": upper_unsat,
        "upper_witness": exact_witness,
        "low_witnesses": low_witnesses,
        "units": [dict(units[key]) for key in sorted(units)],
        # Compatibility counters for the existing Stage-3 pool envelope.  They
        # count semantic SAT units, never fictitious MILP directions.
        "expected_directions": expected_units,
        "completed_directions": terminal,
        "elapsed_s": time.monotonic() - started,
    }
    if termination is not None:
        value["termination"] = dict(termination)
    value["artifact_sha256"] = _canonical_sha256(value)
    return value


def _portfolio_configs(
    requested_solver: str,
    requested_encoding: str,
) -> list[dict[str, str]]:
    """Return a bounded diversity warmup followed by exhaustive fallbacks."""

    normalized_solver = str(requested_solver).lower()
    normalized_encoding = str(requested_encoding).lower()
    encoding_order = [
        "seqcounter",
        "kmtotalizer",
        "native-minicard",
        "totalizer",
    ]
    if normalized_encoding not in encoding_order:
        raise ValueError("unsupported SAT cardinality encoding")
    encoding_order = [normalized_encoding] + [
        encoding for encoding in encoding_order if encoding != normalized_encoding
    ]
    solver_names = (
        list(SAT_AUTO_SOLVERS)
        if normalized_solver == "auto"
        else [normalized_solver]
    )
    # The auto lane begins with four genuinely different solver/encoding
    # families.  This prevents a larger timeout tier from spending every
    # worker on the same CaDiCaL formulation before trying a different search
    # tree.  The finite exhaustive tail remains available after the warmup.
    pairs: list[tuple[str, str]] = []
    if normalized_solver == "auto":
        alternate_encodings = {
            "seqcounter": ("totalizer", "kmtotalizer"),
            "kmtotalizer": ("seqcounter", "totalizer"),
            "totalizer": ("seqcounter", "kmtotalizer"),
            "native-minicard": (
                "seqcounter", "totalizer", "kmtotalizer",
            ),
        }[normalized_encoding]
        if normalized_encoding == "native-minicard":
            pairs.extend([
                ("minicard", "native-minicard"),
                (solver_names[0], alternate_encodings[0]),
                ("kissat404", alternate_encodings[1]),
                ("glucose42", alternate_encodings[2]),
            ])
        else:
            pairs.extend([
                (solver_names[0], normalized_encoding),
                ("kissat404", alternate_encodings[0]),
                ("glucose42", alternate_encodings[1]),
                ("minicard", "native-minicard"),
            ])

    # Native MiniCard is a distinct solver/encoding pair and is never sent to
    # another backend.  Every legal CDCL/encoding pair is retained in the
    # deterministic tail, with duplicates removed below.
    for encoding in encoding_order:
        if encoding == "native-minicard":
            if normalized_solver in {"auto", "minicard"}:
                pairs.append(("minicard", encoding))
        elif normalized_solver != "minicard":
            pairs.append((solver_names[0], encoding))
    if normalized_solver == "auto":
        for name in solver_names[1:]:
            for encoding in encoding_order:
                if encoding != "native-minicard":
                    pairs.append((name, encoding))
    return [
        {"solver": solver_name, "cardinality_encoding": encoding}
        for solver_name, encoding in dict.fromkeys(pairs)
    ]


def _portfolio_for_lower_unit(
    portfolio: list[dict[str, str]],
    lower_unit_ordinal: int,
) -> list[dict[str, str]]:
    """Rotate only the bounded warmup across independent lower units."""

    if lower_unit_ordinal < 0:
        raise ValueError("lower_unit_ordinal must be nonnegative")
    width = min(SAT_DIVERSITY_WARMUP_WIDTH, len(portfolio))
    if width < 2:
        return [dict(config) for config in portfolio]
    offset = lower_unit_ordinal % width
    warmup = portfolio[:width]
    rotated = warmup[offset:] + warmup[:offset]
    return [dict(config) for config in rotated + portfolio[width:]]


def build_anchor_cover_cubes(anchor_indices: tuple[int, ...]) -> list[dict[str, Any]]:
    """Describe a disjoint first-nonzero cover of ``OR(anchor_indices)``.

    Stage 3 runs every cube independently and promotes a logical partition
    only after all cube decisions are complete UNSAT results.
    """

    anchors = tuple(int(index) for index in anchor_indices)
    if not anchors or len(set(anchors)) != len(anchors) or any(
        index < 0 for index in anchors
    ):
        raise ValueError("anchor_indices must be nonempty, distinct, nonnegative")
    cubes: list[dict[str, Any]] = []
    for cube_index, required_one in enumerate(anchors):
        cube: dict[str, Any] = {
            "schema_version": SAT_ANCHOR_CUBE_SCHEMA_VERSION,
            "cover": "anchor-or-first-nonzero-v1",
            "cube_index": cube_index,
            "zero_anchor_indices": list(anchors[:cube_index]),
            "one_anchor_index": required_one,
            "anchor_indices": list(anchors),
        }
        cube["cube_sha256"] = _canonical_sha256(cube)
        cubes.append(cube)
    return cubes


def _attempt_record(
    evidence: Mapping[str, Any],
    *,
    attempt_index: int,
    requested_solver: str,
    requested_encoding: str,
    anchor_cube: Mapping[str, Any] | None = None,
    portfolio_policy: str = SAT_PORTFOLIO_POLICY,
) -> dict[str, Any]:
    if portfolio_policy not in SAT_COMPATIBLE_PORTFOLIO_POLICIES:
        raise ValueError("unsupported SAT portfolio policy")
    backend = evidence.get("backend")
    resolved_solver = (
        backend.get("solver") if isinstance(backend, Mapping) else None
    )
    instance = evidence.get("instance")
    execution = (
        instance.get("solver_execution")
        if isinstance(instance, Mapping)
        else None
    )
    if not isinstance(execution, Mapping):
        execution = evidence.get("incremental_solver")
    if not isinstance(execution, Mapping):
        execution = {}
    execution_policy = str(
        execution.get("policy", SAT_ONE_SHOT_POLICY),
    )
    conflict_budget = execution.get("incremental_conflict_budget")
    if conflict_budget is None:
        conflict_budget = execution.get("conflict_budget_per_slice")
    if evidence.get("evidence_kind") == DISTQLDPC_EVIDENCE_KIND:
        # Attempt history is scheduler metadata.  The external evidence keeps
        # its own exact process policy/argv binding and remains independently
        # replayed; this compatibility envelope records it as one spawned run.
        execution_policy, conflict_budget = SAT_ONE_SHOT_POLICY, None
    record: dict[str, Any] = {
        "schema_version": SAT_ATTEMPT_SCHEMA_VERSION,
        "portfolio_policy": portfolio_policy,
        "attempt_index": int(attempt_index),
        "requested_solver": str(requested_solver),
        "resolved_solver": resolved_solver,
        "cardinality_encoding": str(requested_encoding),
        "execution_policy": execution_policy,
        "incremental_conflict_budget": conflict_budget,
        "hard_timeout_s": evidence.get("hard_timeout_s"),
        "random_seed": evidence.get("random_seed"),
        "outcome": evidence.get("outcome"),
        "decision_complete": evidence.get("decision_complete"),
        "elapsed_s": evidence.get("elapsed_s"),
        # Old hard-timeout evidence did not carry an evidence_sha256.  Its
        # canonical snapshot is still recorded here so the resume decision is
        # auditable inside the atomically hashed Stage-3 artifact.
        "evidence_sha256": evidence.get("evidence_sha256"),
        "evidence_snapshot_sha256": _canonical_sha256(evidence),
        "anchor_cube": None if anchor_cube is None else dict(anchor_cube),
    }
    record["attempt_sha256"] = _canonical_sha256(record)
    return record


def _attempt_valid(record: Mapping[str, Any]) -> bool:
    try:
        execution_policy = record.get(
            "execution_policy", SAT_ONE_SHOT_POLICY,
        )
        conflict_budget = record.get("incremental_conflict_budget")
        execution_valid = bool(
            execution_policy in SAT_EXECUTION_POLICIES
            and (
                (execution_policy == SAT_ONE_SHOT_POLICY and conflict_budget is None)
                or (
                    execution_policy == SAT_INCREMENTAL_POLICY
                    and isinstance(conflict_budget, int)
                    and not isinstance(conflict_budget, bool)
                    and conflict_budget > 0
                )
            )
        )
        return bool(
            record.get("schema_version") == SAT_ATTEMPT_SCHEMA_VERSION
            and record.get("portfolio_policy")
            in SAT_COMPATIBLE_PORTFOLIO_POLICIES
            and execution_valid
            and record.get("attempt_sha256")
            == _canonical_sha256(record, omit="attempt_sha256")
        )
    except (TypeError, ValueError):
        return False


def _legacy_attempt(
    evidence: Mapping[str, Any],
    anchor_cube: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    backend = evidence.get("backend")
    solver_name = (
        str(backend.get("solver", "auto"))
        if isinstance(backend, Mapping)
        else "auto"
    )
    return _attempt_record(
        evidence,
        attempt_index=0,
        requested_solver=solver_name,
        requested_encoding=str(
            evidence.get("cardinality_encoding", "seqcounter"),
        ),
        anchor_cube=anchor_cube,
        portfolio_policy=SAT_PORTFOLIO_POLICY_V1,
    )


def _resume_units(
    output: Path,
    *,
    candidate: Mapping[str, Any],
    mode: str,
    plan: list[tuple[str, str, int | None, int | None]],
    anchor_cover_cubes: list[Mapping[str, Any]] | None,
    translation_symmetry: Mapping[str, Any] | None,
    construction_symmetry: Mapping[str, Any] | None = None,
    logical_detector: Mapping[str, Any],
    xz_sector_isometry: Mapping[str, Any] | None,
    lower_backend: str = DEFAULT_SAT_LOWER_BACKEND,
    hx: np.ndarray | None = None,
    hz: np.ndarray | None = None,
    lx: np.ndarray | None = None,
    lz: np.ndarray | None = None,
) -> dict[str, dict[str, Any]]:
    """Load only an intact, identity-matching partial Stage-3 artifact."""

    if lower_backend not in SAT_LOWER_BACKENDS:
        raise ValueError("unsupported Stage-3 lower backend")
    if lower_backend == "distqldpc" and any(
        matrix is None for matrix in (hx, hz, lx, lz)
    ):
        raise ValueError(
            "DistQLDPC resume replay requires all CSS matrices"
        )
    try:
        value = json.loads(output.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, UnicodeError, json.JSONDecodeError):
        return {}
    if not isinstance(value, Mapping):
        return {}
    try:
        artifact_hash_valid = value.get("artifact_sha256") == _canonical_sha256(
            value,
            omit="artifact_sha256",
        )
    except (TypeError, ValueError):
        artifact_hash_valid = False
    stored_isometry = value.get("xz_sector_isometry")
    isometry_matches = bool(
        stored_isometry == xz_sector_isometry
        # Schema-v1 artifacts created before the explicit isometry report can
        # safely contribute per-unit attempts.  The new plan only imports unit
        # IDs it still requires and recomputes/binds the report itself.
        or stored_isometry is None
    )
    if not (
        artifact_hash_valid
        and value.get("schema_version") == SAT_STAGE3_SCHEMA_VERSION
        and value.get("gate") == SAT_STAGE3_GATE
        and value.get("candidate") == candidate
        and value.get("requested_coverage_mode", value.get("coverage_mode"))
        == mode
        and value.get("translation_symmetry") == translation_symmetry
        and value.get("construction_symmetry") == construction_symmetry
        and value.get("logical_detector") == logical_detector
        and isometry_matches
    ):
        return {}
    expected: dict[
        str,
        tuple[str, str, int | None, Mapping[str, Any] | None],
    ] = {}
    for phase, sector, partition, cube_index in plan:
        cube = (
            None
            if cube_index is None
            else anchor_cover_cubes[cube_index]
        )
        expected[_unit_key(phase, sector, partition, cube)] = (
            phase, sector, partition, cube,
        )
    resumed: dict[str, dict[str, Any]] = {}
    raw_units = value.get("units")
    if not isinstance(raw_units, list):
        return {}
    for raw in raw_units:
        if not isinstance(raw, Mapping):
            continue
        key = raw.get("unit_id")
        if not isinstance(key, str) or key not in expected or key in resumed:
            continue
        phase, sector, partition, expected_cube = expected[key]
        if not (
            raw.get("phase") == phase
            and raw.get("sector") == sector
            and raw.get("partition_index") == partition
            and raw.get("anchor_cube") == expected_cube
            and isinstance(raw.get("solver_evidence"), Mapping)
        ):
            continue
        evidence = dict(raw["solver_evidence"])
        external_mode = _distqldpc_mode_from_phase(phase)
        if external_mode is None:
            if not _evidence_matches_anchor_cube(evidence, expected_cube):
                continue
        else:
            if not (
                lower_backend == "distqldpc"
                and sector == "XZ"
                and partition is None
                and expected_cube is None
                and evidence.get("outcome") in DISTQLDPC_TERMINAL_OUTCOMES
            ):
                continue
            assert hx is not None and hz is not None
            assert lx is not None and lz is not None
            checkpoint_identity = distqldpc_stage3_checkpoint_identity(
                candidate,
                cardinality_mode=external_mode,
                coverage_mode=mode,
                logical_detector=logical_detector,
                translation_symmetry=translation_symmetry,
                construction_symmetry=construction_symmetry,
                xz_sector_isometry=xz_sector_isometry,
            )
            if verify_distqldpc_lower_evidence(
                evidence,
                hx,
                hz,
                lx,
                lz,
                max_weight=int(candidate["required_distance"]) - 1,
                cardinality_mode=external_mode,
                expected_checkpoint_identity=checkpoint_identity,
            ):
                continue
        attempts = raw.get("attempts")
        if attempts is None:
            normalized_attempts = [
                _attempt_record(
                    evidence,
                    attempt_index=0,
                    requested_solver=f"distqldpc-{external_mode}",
                    requested_encoding=f"maxcdcl-{external_mode}",
                )
                if external_mode is not None
                else _legacy_attempt(evidence, expected_cube)
            ]
        elif isinstance(attempts, list) and all(
            isinstance(item, Mapping) and _attempt_valid(item)
            and item.get("anchor_cube") == expected_cube
            for item in attempts
        ):
            normalized_attempts = [dict(item) for item in attempts]
        else:
            continue
        indexes = [item.get("attempt_index") for item in normalized_attempts]
        if (
            not all(isinstance(index, int) and not isinstance(index, bool)
                    for index in indexes)
            or len(indexes) != len(set(indexes))
        ):
            continue
        resumed[key] = {
            "unit_id": key,
            "phase": phase,
            "sector": sector,
            "partition_index": partition,
            "anchor_cube": (
                None if expected_cube is None else dict(expected_cube)
            ),
            "solver_evidence": evidence,
            "attempts": normalized_attempts,
            "checkpoint_replay_pending": (
                evidence.get("outcome") in SAT_TERMINAL_OUTCOMES
                | DISTQLDPC_TERMINAL_OUTCOMES
            ),
        }
    return resumed


def _next_attempt(
    unit: Mapping[str, Any] | None,
    *,
    portfolio: list[dict[str, str]],
    hard_timeout_s: float,
    execution_policy: str = SAT_ONE_SHOT_POLICY,
    incremental_conflict_budget: int | None = None,
) -> tuple[int, dict[str, str], bool] | None:
    """Choose a non-identical retry, or a terminal checkpoint replay."""

    if execution_policy not in SAT_EXECUTION_POLICIES:
        raise ValueError("unsupported SAT execution policy")
    if execution_policy == SAT_ONE_SHOT_POLICY:
        if incremental_conflict_budget is not None:
            raise ValueError("one-shot SAT execution cannot use a conflict budget")
    elif (
        isinstance(incremental_conflict_budget, bool)
        or not isinstance(incremental_conflict_budget, int)
        or incremental_conflict_budget < 1
    ):
        raise ValueError(
            "persistent SAT execution requires a positive conflict budget"
        )
    attempts = (
        list(unit.get("attempts", []))
        if isinstance(unit, Mapping) and isinstance(unit.get("attempts"), list)
        else []
    )
    evidence = (
        unit.get("solver_evidence") if isinstance(unit, Mapping) else None
    )
    if isinstance(evidence, Mapping) and evidence.get("outcome") in (
        SAT_TERMINAL_OUTCOMES | DISTQLDPC_TERMINAL_OUTCOMES
    ):
        backend = evidence.get("backend")
        solver_name = (
            str(backend.get("solver"))
            if isinstance(backend, Mapping) and backend.get("solver")
            else portfolio[0]["solver"]
        )
        encoding = str(
            evidence.get(
                "cardinality_encoding",
                portfolio[0]["cardinality_encoding"],
            ),
        )
        attempt_index = int(
            max(
                (item.get("attempt_index", 0) for item in attempts),
                default=0,
            ),
        )
        return attempt_index, {
            "solver": solver_name,
            "cardinality_encoding": encoding,
        }, True

    history: dict[
        tuple[str, str, str, int | None], list[tuple[Any, float]]
    ] = {}
    for attempt in attempts:
        outcome = attempt.get("outcome")
        if outcome == "cancelled":
            continue
        solver_name = attempt.get("resolved_solver") or attempt.get(
            "requested_solver",
        )
        encoding = attempt.get("cardinality_encoding")
        attempt_policy = attempt.get(
            "execution_policy", SAT_ONE_SHOT_POLICY,
        )
        attempt_conflict_budget = attempt.get("incremental_conflict_budget")
        if attempt_policy == SAT_ONE_SHOT_POLICY:
            attempt_conflict_budget = None
        elif (
            isinstance(attempt_conflict_budget, bool)
            or not isinstance(attempt_conflict_budget, int)
            or attempt_conflict_budget < 1
        ):
            continue
        else:
            attempt_conflict_budget = int(attempt_conflict_budget)
        try:
            old_budget = float(attempt.get("hard_timeout_s"))
        except (TypeError, ValueError):
            old_budget = hard_timeout_s
        if not math.isfinite(old_budget) or old_budget <= 0:
            old_budget = hard_timeout_s
        if (
            isinstance(solver_name, str)
            and isinstance(encoding, str)
            and attempt_policy in SAT_EXECUTION_POLICIES
        ):
            history.setdefault(
                (solver_name, encoding, attempt_policy, attempt_conflict_budget), [],
            ).append(
                (outcome, old_budget),
            )
    next_index = max(
        (int(item.get("attempt_index", -1)) for item in attempts),
        default=-1,
    ) + 1

    warmup_width = min(SAT_DIVERSITY_WARMUP_WIDTH, len(portfolio))
    warmup = portfolio[:warmup_width]
    tail = portfolio[warmup_width:]

    def untried(
        signature: tuple[str, str, str, int | None],
    ) -> bool:
        return signature not in history

    def budget_upgrade(
        signature: tuple[str, str, str, int | None],
    ) -> bool:
        records = history.get(signature, [])
        return bool(
            records
            and all(outcome == "hard_timeout" for outcome, _ in records)
            and max(budget for _, budget in records) < hard_timeout_s
        )

    # Complete a small heterogeneous warmup before spending a larger budget
    # on the same search tree.  Once bounded diversity has been sampled, a new
    # timeout tier may revisit its strongest lanes; the exhaustive tail is the
    # final same-tier/fallback reservoir.
    for configs, predicate in (
        (warmup, untried),
        (warmup, budget_upgrade),
        (tail, untried),
        (tail, budget_upgrade),
    ):
        for config in configs:
            signature = (
                config["solver"],
                config["cardinality_encoding"],
                execution_policy,
                incremental_conflict_budget,
            )
            if predicate(signature):
                return next_index, dict(config), False
    return None


def _checkpoint_path(state_dir: Path, key: str, attempt_index: int) -> Path:
    # Attempt zero retains the deployed filename and binding so previously
    # proven terminal checkpoints survive the scheduler upgrade.
    if attempt_index == 0:
        return state_dir / f"{key}.json"
    return state_dir / f"{key}.attempt-{attempt_index:03d}.json"


def _distqldpc_fair_job_order(
    jobs: list[tuple[Any, ...]],
    *,
    workers: int,
) -> list[tuple[Any, ...]]:
    """Reserve one first-wave slot for an independent PySAT lower lane.

    Checkpoint replays remain first.  At most ``workers - 1`` new external
    lanes precede the first PySAT lower job, so five workers start four MaxCDCL
    searches plus one independent fallback after a fast replay frees its slot.
    Six workers without replays still start all five external modes plus PySAT.
    """

    if isinstance(workers, bool) or not isinstance(workers, int) or workers < 1:
        raise ValueError("workers must be a positive integer")
    replays = [job for job in jobs if bool(job[3])]
    new_jobs = [job for job in jobs if not bool(job[3])]
    external = [
        job for job in new_jobs
        if _distqldpc_mode_from_phase(job[0][0]) is not None
    ]
    non_external = [
        job for job in new_jobs
        if _distqldpc_mode_from_phase(job[0][0]) is None
    ]
    fallback = next(
        (
            job for job in non_external
            if job[0][0] in {"lower-global", "lower"}
        ),
        None,
    )
    if fallback is None:
        return replays + external + non_external
    external_prefix_count = min(len(external), max(0, workers - 1))
    external_prefix = external[:external_prefix_count]
    external_tail = external[external_prefix_count:]
    remaining_non_external = [
        job for job in non_external if job is not fallback
    ]
    return (
        replays
        + external_prefix
        + [fallback]
        + external_tail
        + remaining_non_external
    )


def screen_sat_candidate(
    candidate: dict[str, Any],
    *,
    output: Path,
    timeout: float = 120,
    workers: int = 4,
    threshold_only: bool = False,
    resume: bool = True,
    hard_timeout: float | None = None,
    candidate_timeout: float | None = None,
    termination_grace: float = 2.0,
    coverage_mode: str = "first-nonzero",
    cardinality_encoding: str = "seqcounter",
    solver: str = "auto",
    incremental_conflict_budget: int | None = None,
    lower_backend: str = DEFAULT_SAT_LOWER_BACKEND,
    distqldpc_exe: Path | str = DEFAULT_DISTQLDPC_EXE,
) -> dict[str, Any]:
    """Run X/Z lower partitions and exact-weight witness searches."""

    del threshold_only
    screen_started = time.monotonic()
    if coverage_mode not in SAT_COVERAGE_MODES:
        raise ValueError("coverage_mode must be global or first-nonzero")
    if lower_backend not in SAT_LOWER_BACKENDS:
        raise ValueError("lower_backend must be pysat or distqldpc")
    if isinstance(workers, bool) or not isinstance(workers, int) or workers < 1:
        raise ValueError("workers must be a positive integer")
    unit_timeout = float(timeout if hard_timeout is None else hard_timeout)
    if not math.isfinite(unit_timeout) or unit_timeout <= 0:
        raise ValueError("SAT unit timeout must be positive and finite")
    if (
        isinstance(incremental_conflict_budget, bool)
        or (
            incremental_conflict_budget is not None
            and (
                not isinstance(incremental_conflict_budget, int)
                or incremental_conflict_budget < 1
            )
        )
    ):
        raise ValueError("incremental_conflict_budget must be a positive integer")
    grace = float(termination_grace)
    if not math.isfinite(grace) or grace < 0:
        raise ValueError("termination_grace must be finite and nonnegative")
    if candidate_timeout is not None:
        candidate_budget = float(candidate_timeout)
        if not math.isfinite(candidate_budget) or candidate_budget <= 0:
            raise ValueError("candidate_timeout must be positive and finite")
    else:
        candidate_budget = None

    generic_construction = isinstance(candidate.get("construction"), Mapping)
    # Compact constructions never inherit the BB torus report.  They use an
    # independently replayed adapter-proposed automorphism group; with a valid
    # orbit cover, global logical OR x first-nonzero orbit-anchor cubes is a
    # complete lower-bound cover.  Otherwise they fail safely to unanchored
    # global X/Z decisions.
    if generic_construction:
        coverage_mode = "global"

    code = build_candidate_code(candidate)
    geometry = validate_candidate_parameters(candidate, code)
    hx, hz, lx, lz = (
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    detector = verify_css_logical_detectors(hx, hz, lx, lz)
    if detector.get("verified") is not True:
        raise ValueError("CSS logical detector audit failed")
    generic_symmetry: Mapping[str, Any] | None = None
    if generic_construction:
        symmetry = None
        proof_sectors = ("X", "Z")
        stored_isometry = None
        try:
            generic_symmetry = verify_construction_symmetry(
                candidate, hx, hz,
            )
        except (ImportError, KeyError, TypeError, ValueError, OverflowError):
            generic_symmetry = None
        if (
            isinstance(generic_symmetry, Mapping)
            and generic_symmetry.get("verified") is True
            and generic_symmetry.get("orbits_cover_all_qubits") is True
        ):
            anchors = tuple(
                int(index)
                for index in generic_symmetry["orbit_representatives"]
            )
            anchor_cover_cubes = build_anchor_cover_cubes(anchors)
        else:
            anchors = ()
            anchor_cover_cubes = None
            generic_symmetry = None
    else:
        symmetry = verify_bb_translation_symmetry(candidate)
        if symmetry.get("verified") is not True:
            raise ValueError("BB translation symmetry audit failed")
        isometry = verify_bb_xz_sector_isometry(
            hx,
            hz,
            ell=int(candidate["ell"]),
            m=int(candidate["m"]),
            geometry=candidate_geometry(candidate),
        )
        proof_sectors = (
            ("X",)
            if isometry.get("verified") is True
            else ("X", "Z")
        )
        stored_isometry = isometry if proof_sectors == ("X",) else None
        anchors = tuple(
            int(index) for index in symmetry["orbit_representatives"]
        )
        anchor_cover_cubes = build_anchor_cover_cubes(anchors)
    k = int(geometry["k"])
    plan = _proof_plan(
        coverage_mode,
        k,
        proof_sectors,
        anchor_cover_cubes,
        lower_backend,
    )
    portfolio = _portfolio_configs(solver, cardinality_encoding)
    execution_policy = (
        SAT_ONE_SHOT_POLICY
        if incremental_conflict_budget is None
        else SAT_INCREMENTAL_POLICY
    )
    if incremental_conflict_budget is not None:
        portfolio = [
            config for config in portfolio
            if config["solver"] in SAT_INCREMENTAL_SOLVERS
        ]
        if not portfolio:
            raise ValueError("no safe incremental SAT solver remains in the portfolio")
    state_dir = output.parent / "sat-units" / hashlib.sha256(
        str(candidate["canonical_digest"]).encode(),
    ).hexdigest()
    units = (
        _resume_units(
            output,
            candidate=candidate,
            mode=coverage_mode,
            plan=plan,
            anchor_cover_cubes=anchor_cover_cubes,
            translation_symmetry=symmetry,
            construction_symmetry=generic_symmetry,
            logical_detector=detector,
            xz_sector_isometry=stored_isometry,
            lower_backend=lower_backend,
            hx=hx,
            hz=hz,
            lx=lx,
            lz=lz,
        )
        if resume else {}
    )
    termination: dict[str, Any] | None = None
    cancellation = threading.Event()

    def solve_unit(
        job: tuple[
            tuple[str, str, int | None, int | None],
            int,
            dict[str, str],
            bool,
        ],
    ) -> tuple[str, dict[str, Any], bool]:
        spec, attempt_index, config, checkpoint_replay = job
        phase, sector, partition, cube_index = spec
        anchor_cube = (
            None
            if cube_index is None
            else anchor_cover_cubes[cube_index]
        )
        max_weight = int(candidate["required_distance"]) - (phase != "upper")
        key = _unit_key(phase, sector, partition, anchor_cube)
        remaining = max(0.001, work_deadline - time.monotonic())
        attempt_timeout = min(unit_timeout, remaining)
        external_mode = _distqldpc_mode_from_phase(phase)
        if external_mode is not None:
            if not (
                lower_backend == "distqldpc"
                and sector == "XZ"
                and partition is None
                and anchor_cube is None
            ):
                raise ValueError("invalid DistQLDPC Stage-3 unit specification")
            checkpoint_identity = distqldpc_stage3_checkpoint_identity(
                candidate,
                cardinality_mode=external_mode,
                coverage_mode=coverage_mode,
                logical_detector=detector,
                translation_symmetry=symmetry,
                construction_symmetry=generic_symmetry,
                xz_sector_isometry=stored_isometry,
            )
            evidence = solve_css_distance_distqldpc_lower(
                hx,
                hz,
                lx,
                lz,
                max_weight=max_weight,
                timeout=attempt_timeout,
                binary=distqldpc_exe,
                cardinality_mode=external_mode,
                checkpoint_path=_checkpoint_path(
                    state_dir, key, attempt_index,
                ),
                progress_path=state_dir / f"{key}.progress.json",
                checkpoint_identity=checkpoint_identity,
                resume=resume,
                cancel_event=cancellation,
                termination_grace_s=grace,
            )
        else:
            checks, logicals, _ = _sector_matrices(
                sector, hx, hz, lx, lz,
            )
            checkpoint_identity = {
                "stage3_gate": SAT_STAGE3_GATE,
                "candidate_digest": candidate["canonical_digest"],
                "target_mode": candidate.get("target_mode"),
                "target_binding_sha256": (
                    candidate.get("target", {}).get("binding_sha256")
                    if isinstance(candidate.get("target"), Mapping)
                    else None
                ),
                "phase": phase,
                "coverage_mode": coverage_mode,
                "logical_detector_sha256": detector["report_sha256"],
                "translation_symmetry": symmetry,
                "construction_symmetry_sha256": (
                    None
                    if generic_symmetry is None
                    else generic_symmetry.get("report_sha256")
                ),
                "xz_sector_isometry_sha256": (
                    None
                    if stored_isometry is None
                    else stored_isometry["report_sha256"]
                ),
                **({} if anchor_cube is None else {
                    "anchor_cube_sha256": anchor_cube["cube_sha256"],
                }),
            }
            evidence = solve_css_sector_sat(
                checks,
                logicals,
                max_weight=max_weight,
                timeout=attempt_timeout,
                workers=1,
                seed=attempt_index,
                partition_index=partition,
                anchor_indices=anchors,
                zero_anchor_indices=(
                    None
                    if anchor_cube is None
                    else tuple(anchor_cube["zero_anchor_indices"])
                ),
                one_anchor_index=(
                    None
                    if anchor_cube is None
                    else anchor_cube["one_anchor_index"]
                ),
                anchor_cube_sha256=(
                    None
                    if anchor_cube is None
                    else anchor_cube["cube_sha256"]
                ),
                sector=sector,
                cardinality_encoding=config["cardinality_encoding"],
                solver=config["solver"],
                incremental_conflict_budget=incremental_conflict_budget,
                checkpoint_path=_checkpoint_path(
                    state_dir, key, attempt_index,
                ),
                resume=resume,
                checkpoint_identity=checkpoint_identity,
                cancel_event=cancellation,
                termination_grace_s=grace,
            )
            if evidence.get("outcome") == "sat":
                failures = verify_css_threshold_sat_witness(
                    evidence, checks, logicals,
                )
                if failures:
                    evidence = {
                        **evidence,
                        "outcome": "solver_error",
                        "decision_complete": False,
                        "threshold_infeasible": False,
                        "retryable": True,
                        "message": (
                            "witness replay failed: " + "; ".join(failures)
                        ),
                    }
                    evidence["evidence_sha256"] = _canonical_sha256(
                        evidence,
                        omit="evidence_sha256",
                    )
        previous = units.get(key)
        attempts = (
            [dict(item) for item in previous.get("attempts", [])]
            if isinstance(previous, Mapping)
            and isinstance(previous.get("attempts"), list)
            else []
        )
        # A checkpoint replay is not a new solver attempt.  If the supposedly
        # terminal checkpoint vanished or failed binding validation, the call
        # really solved again and must be recorded as a fresh attempt.
        was_replayed = bool(
            checkpoint_replay and evidence.get("resumed") is True
        )
        if not was_replayed:
            recorded_index = attempt_index
            matching_record = next((
                index
                for index, item in enumerate(attempts)
                if item.get("attempt_index") == recorded_index
            ), None)
            if matching_record is not None and checkpoint_replay:
                # The artifact claimed a terminal unit but its checkpoint was
                # absent/invalid, so the solver rebuilt exactly that attempt
                # and atomically recreated the same checkpoint path.
                attempts.pop(matching_record)
            elif matching_record is not None:
                recorded_index = max(
                    (int(item.get("attempt_index", -1)) for item in attempts),
                    default=-1,
                ) + 1
            attempts.append(_attempt_record(
                evidence,
                attempt_index=recorded_index,
                requested_solver=config["solver"],
                requested_encoding=config["cardinality_encoding"],
                anchor_cube=anchor_cube,
            ))
        return key, {
            "unit_id": key,
            "phase": phase,
            "sector": sector,
            "partition_index": partition,
            "anchor_cube": (
                None if anchor_cube is None else dict(anchor_cube)
            ),
            "solver_evidence": evidence,
            "attempts": attempts,
        }, was_replayed

    def write_progress() -> dict[str, Any]:
        value = _artifact(
            candidate,
            mode=coverage_mode,
            translation_symmetry=symmetry,
            construction_symmetry=generic_symmetry,
            logical_detector=detector,
            units=units,
            expected_units=len(plan),
            started=screen_started,
            termination=termination,
            xz_sector_isometry=stored_isometry,
            proof_sectors=proof_sectors,
            anchor_cover_cubes=anchor_cover_cubes,
            lower_backend=lower_backend,
            hx=hx,
            hz=hz,
            lx=lx,
            lz=lz,
        )
        _atomic_write_json(output, value)
        return value

    jobs: list[
        tuple[
            tuple[str, str, int | None, int | None],
            int,
            dict[str, str],
            bool,
        ]
    ] = []
    exhausted_units: list[str] = []
    lower_unit_ordinal = 0
    for spec in plan:
        phase, sector, partition, cube_index = spec
        cube = (
            None if cube_index is None else anchor_cover_cubes[cube_index]
        )
        key = _unit_key(phase, sector, partition, cube)
        external_mode = _distqldpc_mode_from_phase(phase)
        if external_mode is not None:
            unit_portfolio = [{
                "solver": f"distqldpc-{external_mode}",
                "cardinality_encoding": f"maxcdcl-{external_mode}",
            }]
            unit_execution_policy = SAT_ONE_SHOT_POLICY
            unit_conflict_budget = None
        else:
            unit_portfolio = portfolio
            unit_execution_policy = execution_policy
            unit_conflict_budget = incremental_conflict_budget
            if phase == "lower":
                unit_portfolio = _portfolio_for_lower_unit(
                    portfolio,
                    lower_unit_ordinal,
                )
                lower_unit_ordinal += 1
        selected = _next_attempt(
            units.get(key),
            portfolio=unit_portfolio,
            hard_timeout_s=unit_timeout,
            execution_policy=unit_execution_policy,
            incremental_conflict_budget=unit_conflict_budget,
        )
        if selected is None:
            exhausted_units.append(key)
            continue
        attempt_index, config, checkpoint_replay = selected
        jobs.append((spec, attempt_index, config, checkpoint_replay))

    # Replay terminal checkpoints first.  Five independent MaxCDCL encodings
    # lead new work, followed by PySAT global/partition fallbacks and upper
    # witness searches.  With six workers this admits all external lanes plus
    # one independent PySAT lower lane without nested solver portfolios.
    def job_priority(job: tuple[Any, ...]) -> tuple[int, int, int]:
        spec, _attempt_index, _config, replay = job
        phase, _sector, _partition, cube_index = spec
        cube = (
            None if cube_index is None else anchor_cover_cubes[cube_index]
        )
        previous = units.get(_unit_key(phase, _sector, _partition, cube))
        attempt_count = (
            len(previous.get("attempts", []))
            if isinstance(previous, Mapping)
            and isinstance(previous.get("attempts"), list)
            else 0
        )
        if _distqldpc_mode_from_phase(phase) is not None:
            phase_priority = 0
        elif phase == "lower-global":
            phase_priority = 1
        elif phase == "lower":
            phase_priority = 2
        else:
            phase_priority = 3
        return (0 if replay else 1, phase_priority, attempt_count)

    jobs.sort(key=job_priority)
    if lower_backend == "distqldpc":
        jobs = _distqldpc_fair_job_order(jobs, workers=workers)
    if candidate_budget is None:
        waves = math.ceil(max(1, len(jobs)) / workers)
        per_wave_margin = max(SAT_CANDIDATE_DEADLINE_SLACK_S, grace)
        candidate_budget = (
            waves * (unit_timeout + per_wave_margin)
            + grace
            + SAT_CANDIDATE_DEADLINE_SLACK_S
        )
    candidate_deadline = screen_started + candidate_budget
    work_deadline = max(screen_started, candidate_deadline - grace)
    if exhausted_units:
        termination = {
            "reason": "portfolio_exhausted",
            "retryable": True,
            "units": exhausted_units,
            "unit_timeout_s": unit_timeout,
            "message": (
                "all distinct solver/encoding attempts at this timeout were "
                "already tried; increase the timeout or extend the portfolio"
            ),
        }
    artifact = write_progress()
    if artifact["status"] in {"REJECTED", "THRESHOLD_PROVEN", "EXACT_PROVEN"}:
        return artifact
    if not jobs:
        return artifact

    queue = deque(jobs)
    executor = ThreadPoolExecutor(max_workers=min(workers, len(jobs)))
    active: dict[Any, tuple[Any, ...]] = {}
    try:
        while queue and len(active) < workers and time.monotonic() < work_deadline:
            job = queue.popleft()
            active[executor.submit(solve_unit, job)] = job
        while active:
            remaining = work_deadline - time.monotonic()
            if remaining <= 0:
                cancellation.set()
                if termination is None or termination.get("reason") != "portfolio_exhausted":
                    termination = {
                        "reason": "candidate_timeout",
                        "retryable": True,
                        "candidate_timeout_s": candidate_budget,
                        "unit_timeout_s": unit_timeout,
                        "queued_units": [
                            _unit_key(
                                job[0][0],
                                job[0][1],
                                job[0][2],
                                (
                                    None
                                    if job[0][3] is None
                                    else anchor_cover_cubes[job[0][3]]
                                ),
                            )
                            for job in queue
                        ],
                    }
            done, _ = wait(
                active,
                timeout=max(0.0, min(remaining, 0.25)),
                return_when=FIRST_COMPLETED,
            )
            if not done:
                continue
            for future in done:
                active.pop(future)
                key, result, _was_replayed = future.result()
                units[key] = result
                artifact = write_progress()
                terminal = artifact["status"] in {
                    "REJECTED", "THRESHOLD_PROVEN", "EXACT_PROVEN",
                }
                fatal_conflict = artifact.get("distqldpc_conflict") is True
                if terminal or fatal_conflict:
                    cancellation.set()
                    queue.clear()
                elif not cancellation.is_set() and queue:
                    next_job = queue.popleft()
                    active[executor.submit(solve_unit, next_job)] = next_job
        if cancellation.is_set():
            # Futures already running observe the event and reap their own SAT
            # children.  No queued job is submitted after the terminal fact or
            # candidate deadline.
            for future in active:
                future.cancel()
    finally:
        cancellation.set()
        executor.shutdown(wait=True, cancel_futures=True)
    return write_progress()


__all__ = [
    "DEFAULT_SAT_LOWER_BACKEND",
    "DISTQLDPC_PHASE_PREFIX",
    "SAT_ANCHOR_CUBE_SCHEMA_VERSION",
    "SAT_CANDIDATE_DEADLINE_SLACK_S",
    "SAT_COMPATIBLE_PORTFOLIO_POLICIES",
    "SAT_LOWER_BACKENDS",
    "SAT_COVERAGE_MODES",
    "SAT_DIVERSITY_WARMUP_WIDTH",
    "SAT_PORTFOLIO_POLICY",
    "SAT_PORTFOLIO_POLICY_V1",
    "SAT_STAGE3_GATE",
    "SAT_STAGE3_SCHEMA_VERSION",
    "build_anchor_cover_cubes",
    "screen_sat_candidate",
    "distqldpc_stage3_checkpoint_identity",
    "verify_css_logical_detectors",
]
