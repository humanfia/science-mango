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
from evaluation.geometry import candidate_geometry
from evaluation.distance_sat import (
    SAT_AUTO_SOLVERS,
    SAT_EVIDENCE_KIND,
    SAT_EVIDENCE_SCHEMA_VERSION,
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
SAT_PORTFOLIO_POLICY = "lower-fair-solver-encoding-portfolio-v1"
SAT_ATTEMPT_SCHEMA_VERSION = 1
SAT_ANCHOR_CUBE_SCHEMA_VERSION = 1


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
        and isinstance(cnf, Mapping)
        and cnf.get("anchor_unit_clauses_sha256")
        == _canonical_sha256(clauses)
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


def _proof_plan(
    mode: str,
    k: int,
    sectors: tuple[str, ...] = ("X", "Z"),
    anchor_cover_cubes: list[Mapping[str, Any]] | None = None,
) -> list[tuple[str, str, int | None, int | None]]:
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
    return global_lower + lower + upper


def _artifact(
    candidate: Mapping[str, Any],
    *,
    mode: str,
    translation_symmetry: Mapping[str, Any],
    logical_detector: Mapping[str, Any],
    units: Mapping[str, Mapping[str, Any]],
    expected_units: int,
    started: float,
    termination: Mapping[str, Any] | None = None,
    xz_sector_isometry: Mapping[str, Any] | None = None,
    proof_sectors: tuple[str, ...] = ("X", "Z"),
    anchor_cover_cubes: list[Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    required = int(candidate["required_distance"])
    k = int(candidate["k"])
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
        if evidence.get("outcome") in {"sat", "unsat"}:
            terminal += 1
        elif evidence.get("retryable") is True:
            retryable += 1
        phase = unit.get("phase")
        sector = unit.get("sector")
        partition = unit.get("partition_index")
        unit_cube = unit.get("anchor_cube")
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
    if low_witnesses:
        status = "REJECTED"
    elif (lower_complete or global_lower_complete) and exact_witness is not None:
        status = "EXACT_PROVEN"
    elif lower_complete or global_lower_complete or upper_unsat_complete:
        status = "THRESHOLD_PROVEN"
    else:
        status = "UNRESOLVED"
    global_route_complete = upper_unsat_complete or global_lower_complete
    effective_mode = "global" if global_route_complete else mode
    if upper_unsat_complete:
        effective_lower = [
            upper_unsat_by_sector[sector] for sector in proof_sectors
        ]
    elif global_lower_complete:
        effective_lower = [
            global_lower_by_sector[sector] for sector in proof_sectors
        ]
    else:
        effective_lower = lower
    lower_bound_threshold = required if upper_unsat_complete else required - 1
    effective_expected_lower = (
        len(proof_sectors) if global_route_complete else expected_lower
    )
    effective_expected_partitions = (
        len(proof_sectors)
        if global_route_complete
        else expected_lower_partitions
    )
    effective_completed_partitions = (
        len(proof_sectors)
        if global_route_complete
        else len(completed_partition_keys)
    )
    value: dict[str, Any] = {
        "schema_version": SAT_STAGE3_SCHEMA_VERSION,
        "gate": SAT_STAGE3_GATE,
        "status": status,
        "candidate": dict(candidate),
        "required_distance": required,
        "coverage_mode": effective_mode,
        "requested_coverage_mode": mode,
        "anchor_cover_cubes": None if global_route_complete else requested_cubes,
        "requested_anchor_cover_cubes": requested_cubes,
        "lower_bound_threshold": lower_bound_threshold,
        "threshold_only": False,
        "translation_symmetry": dict(translation_symmetry),
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
    """Return distinct solver/encoding attempts in deterministic order."""

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
    # First vary the cardinality mechanism on the preferred solver.  Native
    # MiniCard is a distinct solver/encoding pair and is never sent to another
    # backend.  Remaining CDCL engines are fallback lanes for the three CNF
    # encodings.
    pairs: list[tuple[str, str]] = []
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
) -> dict[str, Any]:
    backend = evidence.get("backend")
    resolved_solver = (
        backend.get("solver") if isinstance(backend, Mapping) else None
    )
    record: dict[str, Any] = {
        "schema_version": SAT_ATTEMPT_SCHEMA_VERSION,
        "portfolio_policy": SAT_PORTFOLIO_POLICY,
        "attempt_index": int(attempt_index),
        "requested_solver": str(requested_solver),
        "resolved_solver": resolved_solver,
        "cardinality_encoding": str(requested_encoding),
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
        return bool(
            record.get("schema_version") == SAT_ATTEMPT_SCHEMA_VERSION
            and record.get("portfolio_policy") == SAT_PORTFOLIO_POLICY
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
    )


def _resume_units(
    output: Path,
    *,
    candidate: Mapping[str, Any],
    mode: str,
    plan: list[tuple[str, str, int | None, int | None]],
    anchor_cover_cubes: list[Mapping[str, Any]],
    translation_symmetry: Mapping[str, Any],
    logical_detector: Mapping[str, Any],
    xz_sector_isometry: Mapping[str, Any] | None,
) -> dict[str, dict[str, Any]]:
    """Load only an intact, identity-matching partial Stage-3 artifact."""

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
        if not _evidence_matches_anchor_cube(evidence, expected_cube):
            continue
        attempts = raw.get("attempts")
        if attempts is None:
            normalized_attempts = [_legacy_attempt(evidence, expected_cube)]
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
            ),
        }
    return resumed


def _next_attempt(
    unit: Mapping[str, Any] | None,
    *,
    portfolio: list[dict[str, str]],
    hard_timeout_s: float,
) -> tuple[int, dict[str, str], bool] | None:
    """Choose a non-identical retry, or a terminal checkpoint replay."""

    attempts = (
        list(unit.get("attempts", []))
        if isinstance(unit, Mapping) and isinstance(unit.get("attempts"), list)
        else []
    )
    evidence = (
        unit.get("solver_evidence") if isinstance(unit, Mapping) else None
    )
    if isinstance(evidence, Mapping) and evidence.get("outcome") in (
        SAT_TERMINAL_OUTCOMES
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

    exhausted: set[tuple[str, str]] = set()
    for attempt in attempts:
        outcome = attempt.get("outcome")
        if outcome == "cancelled":
            continue
        solver_name = attempt.get("resolved_solver") or attempt.get(
            "requested_solver",
        )
        encoding = attempt.get("cardinality_encoding")
        try:
            old_budget = float(attempt.get("hard_timeout_s"))
        except (TypeError, ValueError):
            old_budget = hard_timeout_s
        if (
            isinstance(solver_name, str)
            and isinstance(encoding, str)
            and (
                outcome != "hard_timeout"
                or old_budget >= hard_timeout_s
            )
        ):
            exhausted.add((solver_name, encoding))
    next_index = max(
        (int(item.get("attempt_index", -1)) for item in attempts),
        default=-1,
    ) + 1
    for config in portfolio:
        signature = (config["solver"], config["cardinality_encoding"])
        if signature not in exhausted:
            return next_index, dict(config), False
    return None


def _checkpoint_path(state_dir: Path, key: str, attempt_index: int) -> Path:
    # Attempt zero retains the deployed filename and binding so previously
    # proven terminal checkpoints survive the scheduler upgrade.
    if attempt_index == 0:
        return state_dir / f"{key}.json"
    return state_dir / f"{key}.attempt-{attempt_index:03d}.json"


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
) -> dict[str, Any]:
    """Run X/Z lower partitions and exact-weight witness searches."""

    del threshold_only
    screen_started = time.monotonic()
    if coverage_mode not in SAT_COVERAGE_MODES:
        raise ValueError("coverage_mode must be global or first-nonzero")
    if isinstance(workers, bool) or not isinstance(workers, int) or workers < 1:
        raise ValueError("workers must be a positive integer")
    unit_timeout = float(timeout if hard_timeout is None else hard_timeout)
    if not math.isfinite(unit_timeout) or unit_timeout <= 0:
        raise ValueError("SAT unit timeout must be positive and finite")
    grace = float(termination_grace)
    if not math.isfinite(grace) or grace < 0:
        raise ValueError("termination_grace must be finite and nonnegative")
    if candidate_timeout is not None:
        candidate_budget = float(candidate_timeout)
        if not math.isfinite(candidate_budget) or candidate_budget <= 0:
            raise ValueError("candidate_timeout must be positive and finite")
    else:
        candidate_budget = None

    code = build_candidate_code(candidate)
    geometry = validate_candidate_parameters(candidate, code)
    hx, hz, lx, lz = (
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    detector = verify_css_logical_detectors(hx, hz, lx, lz)
    if detector.get("verified") is not True:
        raise ValueError("CSS logical detector audit failed")
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
    anchors = tuple(int(index) for index in symmetry["orbit_representatives"])
    anchor_cover_cubes = build_anchor_cover_cubes(anchors)
    k = int(geometry["k"])
    plan = _proof_plan(
        coverage_mode,
        k,
        proof_sectors,
        anchor_cover_cubes,
    )
    portfolio = _portfolio_configs(solver, cardinality_encoding)
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
            logical_detector=detector,
            xz_sector_isometry=stored_isometry,
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
        checks, logicals, _ = _sector_matrices(sector, hx, hz, lx, lz)
        max_weight = int(candidate["required_distance"]) - (phase != "upper")
        key = _unit_key(phase, sector, partition, anchor_cube)
        remaining = max(0.001, work_deadline - time.monotonic())
        attempt_timeout = min(unit_timeout, remaining)
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
                None if anchor_cube is None else anchor_cube["one_anchor_index"]
            ),
            anchor_cube_sha256=(
                None if anchor_cube is None else anchor_cube["cube_sha256"]
            ),
            sector=sector,
            cardinality_encoding=config["cardinality_encoding"],
            solver=config["solver"],
            checkpoint_path=_checkpoint_path(state_dir, key, attempt_index),
            resume=resume,
            checkpoint_identity={
                "stage3_gate": SAT_STAGE3_GATE,
                "candidate_digest": candidate["canonical_digest"],
                "phase": phase,
                "coverage_mode": coverage_mode,
                "logical_detector_sha256": detector["report_sha256"],
                "translation_symmetry": symmetry,
                "xz_sector_isometry_sha256": (
                    None
                    if stored_isometry is None
                    else stored_isometry["report_sha256"]
                ),
                **({} if anchor_cube is None else {
                    "anchor_cube_sha256": anchor_cube["cube_sha256"],
                }),
            },
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
                    "message": "witness replay failed: " + "; ".join(failures),
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
            logical_detector=detector,
            units=units,
            expected_units=len(plan),
            started=screen_started,
            termination=termination,
            xz_sector_isometry=stored_isometry,
            proof_sectors=proof_sectors,
            anchor_cover_cubes=anchor_cover_cubes,
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
    for spec in plan:
        phase, sector, partition, cube_index = spec
        cube = (
            None if cube_index is None else anchor_cover_cubes[cube_index]
        )
        key = _unit_key(phase, sector, partition, cube)
        selected = _next_attempt(
            units.get(key),
            portfolio=portfolio,
            hard_timeout_s=unit_timeout,
        )
        if selected is None:
            exhausted_units.append(key)
            continue
        attempt_index, config, checkpoint_replay = selected
        jobs.append((spec, attempt_index, config, checkpoint_replay))

    # Replay terminal checkpoints first.  New lower units then precede lower
    # retries, with X/Z already interleaved by _proof_plan; upper witness work
    # follows all lower-bound work.  This prevents an exact-witness search
    # from monopolizing a scarce lower-bound worker.
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
        phase_priority = 0 if phase == "lower-global" else (1 if phase == "lower" else 2)
        return (0 if replay else 1, phase_priority, attempt_count)

    jobs.sort(key=job_priority)
    if candidate_budget is None:
        candidate_budget = (
            math.ceil(max(1, len(jobs)) / workers) * unit_timeout + grace + 1.0
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
                if terminal:
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
    "SAT_ANCHOR_CUBE_SCHEMA_VERSION",
    "SAT_COVERAGE_MODES",
    "SAT_PORTFOLIO_POLICY",
    "SAT_STAGE3_GATE",
    "SAT_STAGE3_SCHEMA_VERSION",
    "build_anchor_cover_cubes",
    "screen_sat_candidate",
    "verify_css_logical_detectors",
]
