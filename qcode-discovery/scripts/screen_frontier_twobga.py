#!/usr/bin/env python3
"""Screen one BB candidate through a strict single-block subsystem lane.

Only candidates satisfying the replayed rank-defect hypotheses of
Lin--Pryadko Statement 5 enter the 180-qubit SAT problems.  Auxiliary SAT
witnesses are deliberately inconclusive for the original 360-qubit code;
only two complete auxiliary UNSAT decisions can promote a lower bound.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import threading
import time
import uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Mapping

import numpy as np

from evaluation.distance_milp import get_code_matrices
from evaluation.distance_sat import (
    SAT_EVIDENCE_KIND,
    SAT_EVIDENCE_SCHEMA_VERSION,
    SAT_TERMINAL_OUTCOMES,
    solve_css_sector_sat,
    verify_css_threshold_sat_witness,
)
from evaluation.twobga_subsystem import derive_twobga_subsystem_problem
from scripts.screen_frontier_candidate import (
    build_candidate_code,
    validate_candidate_parameters,
)
from scripts.screen_frontier_sat import verify_css_logical_detectors
from scripts.screen_frontier_xor import verify_bb_translation_symmetry


TWOBGA_STAGE3_GATE = "qldpc-frontier-twobga-subsystem-screen"
TWOBGA_STAGE3_SCHEMA_VERSION = 1
TWOBGA_STAGE3_BACKEND = "twobga-aux"
TWOBGA_PROOF_SECTORS = ("X", "Z")
TWOBGA_REQUEST_FIELD = "_twobga_aux_certificate"
TWOBGA_EXACT_PROOF_TYPE = "qldpc-css-twobga-subsystem-exact-proof-v1"
TWOBGA_BOUND_INSUFFICIENT_STATUS = "BOUND_INSUFFICIENT"
TWOBGA_EXACTNESS_GAP_STATUS = "EXACTNESS_GAP"


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


def _evidence_hash_valid(evidence: Mapping[str, Any]) -> bool:
    try:
        return evidence.get("evidence_sha256") == _canonical_sha256(
            evidence, omit="evidence_sha256",
        )
    except (TypeError, ValueError):
        return False


def _sat_array_sha256(name: str, matrix: np.ndarray) -> str:
    value = np.ascontiguousarray(np.asarray(matrix, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(name.encode())
    digest.update(b"\0")
    digest.update(json.dumps(list(value.shape), separators=(",", ":")).encode())
    digest.update(b"\0")
    digest.update(value.tobytes(order="C"))
    return digest.hexdigest()


def _complete_unsat(evidence: Mapping[str, Any], max_weight: int) -> bool:
    return bool(
        evidence.get("schema_version") == SAT_EVIDENCE_SCHEMA_VERSION
        and evidence.get("evidence_kind") == SAT_EVIDENCE_KIND
        and evidence.get("outcome") == "unsat"
        and evidence.get("decision_complete") is True
        and evidence.get("threshold_infeasible") is True
        and evidence.get("max_weight") == max_weight
        and evidence.get("operator") is None
        and evidence.get("objective") is None
        and _evidence_hash_valid(evidence)
    )


def _complete_sat(evidence: Mapping[str, Any], max_weight: int) -> bool:
    objective = evidence.get("objective")
    return bool(
        evidence.get("schema_version") == SAT_EVIDENCE_SCHEMA_VERSION
        and evidence.get("evidence_kind") == SAT_EVIDENCE_KIND
        and evidence.get("outcome") == "sat"
        and evidence.get("decision_complete") is True
        and evidence.get("threshold_infeasible") is False
        and evidence.get("max_weight") == max_weight
        and isinstance(objective, int)
        and not isinstance(objective, bool)
        and 0 < objective <= max_weight
        and _evidence_hash_valid(evidence)
    )


def _instance_bound(
    evidence: Mapping[str, Any],
    checks: np.ndarray,
    detectors: np.ndarray,
    *,
    sector: str,
    max_weight: int,
    anchors: tuple[int, ...],
) -> bool:
    instance = evidence.get("instance")
    backend = evidence.get("backend")
    return bool(
        isinstance(instance, Mapping)
        and instance.get("check_matrix_sha256")
        == _sat_array_sha256("checks", checks)
        and instance.get("target_logicals_sha256")
        == _sat_array_sha256("logicals", detectors)
        and instance.get("partition_index") is None
        and instance.get("anchor_indices") == list(anchors)
        and instance.get("zero_anchor_indices", []) == []
        and instance.get("one_anchor_index") is None
        and instance.get("anchor_cube_sha256") is None
        and evidence.get("sector") == sector
        and evidence.get("max_weight") == max_weight
        and evidence.get("partition_index") is None
        and evidence.get("anchor_indices") == list(anchors)
        and evidence.get("zero_anchor_indices", []) == []
        and evidence.get("one_anchor_index") is None
        and evidence.get("anchor_cube_sha256") is None
        and isinstance(backend, Mapping)
        and backend.get("distribution") == "python-sat"
        and isinstance(backend.get("solver"), str)
        and bool(backend.get("solver"))
        and _evidence_hash_valid(evidence)
    )


def _valid_auxiliary_lower(
    wrapper: Mapping[str, Any],
    problem,
    *,
    sector: str,
    required_distance: int,
) -> bool:
    checks, detectors, _gauge = problem.sector_matrices(sector)
    symmetry = problem.report["sectors"][sector]["translation_symmetry"]
    anchors = (0,) if symmetry.get("verified") is True else ()
    evidence = wrapper.get("solver_evidence")
    return bool(
        wrapper.get("unit_id") == f"aux-lower-{sector}"
        and wrapper.get("domain") == "auxiliary-subsystem"
        and wrapper.get("phase") == "lower"
        and wrapper.get("sector") == sector
        and wrapper.get("max_weight") == required_distance - 1
        and wrapper.get("anchor_indices") == list(anchors)
        and isinstance(evidence, Mapping)
        and _complete_unsat(evidence, required_distance - 1)
        and _instance_bound(
            evidence,
            checks,
            detectors,
            sector=sector,
            max_weight=required_distance - 1,
            anchors=anchors,
        )
    )


def _valid_original_upper(
    wrapper: Mapping[str, Any],
    *,
    hz: np.ndarray,
    lz: np.ndarray,
    required_distance: int,
    anchors: tuple[int, ...],
) -> bool:
    evidence = wrapper.get("solver_evidence")
    if not (
        wrapper.get("unit_id") == "original-upper-X"
        and wrapper.get("domain") == "original-code"
        and wrapper.get("phase") == "upper"
        and wrapper.get("sector") == "X"
        and wrapper.get("max_weight") == required_distance
        and wrapper.get("anchor_indices") == list(anchors)
        and wrapper.get("witness_verified") is True
        and wrapper.get("witness_failures") == []
        and isinstance(evidence, Mapping)
        and evidence.get("outcome") == "sat"
        and evidence.get("decision_complete") is True
        and evidence.get("objective") == required_distance
        and _instance_bound(
            evidence,
            hz,
            lz,
            sector="X",
            max_weight=required_distance,
            anchors=anchors,
        )
    ):
        return False
    return not verify_css_threshold_sat_witness(evidence, hz, lz)


def _valid_original_counterexample(
    wrapper: Mapping[str, Any],
    *,
    hz: np.ndarray,
    lz: np.ndarray,
    required_distance: int,
    anchors: tuple[int, ...],
) -> bool:
    """Validate an original-code witness strictly below the win threshold."""

    evidence = wrapper.get("solver_evidence")
    objective = evidence.get("objective") if isinstance(evidence, Mapping) else None
    if not (
        wrapper.get("unit_id") == "original-upper-X"
        and wrapper.get("domain") == "original-code"
        and wrapper.get("phase") == "upper"
        and wrapper.get("sector") == "X"
        and wrapper.get("max_weight") == required_distance
        and wrapper.get("anchor_indices") == list(anchors)
        and wrapper.get("witness_verified") is True
        and wrapper.get("witness_failures") == []
        and isinstance(evidence, Mapping)
        and evidence.get("outcome") == "sat"
        and evidence.get("decision_complete") is True
        and isinstance(objective, int)
        and not isinstance(objective, bool)
        and 0 < objective < required_distance
        and _instance_bound(
            evidence,
            hz,
            lz,
            sector="X",
            max_weight=required_distance,
            anchors=anchors,
        )
    ):
        return False
    return not verify_css_threshold_sat_witness(evidence, hz, lz)


def validate_twobga_stage3_artifact(
    artifact: Mapping[str, Any],
) -> dict[str, Any]:
    """Rebuild and fail-closed validate one terminal auxiliary artifact."""

    if (
        artifact.get("schema_version") != TWOBGA_STAGE3_SCHEMA_VERSION
        or artifact.get("gate") != TWOBGA_STAGE3_GATE
        or artifact.get("backend") != TWOBGA_STAGE3_BACKEND
        or artifact.get("status") not in {"THRESHOLD_PROVEN", "EXACT_PROVEN"}
        or artifact.get("artifact_sha256")
        != _canonical_sha256(artifact, omit="artifact_sha256")
    ):
        raise ValueError("not a terminal 2BGA subsystem Stage 3 artifact")
    candidate = artifact.get("candidate")
    if not isinstance(candidate, Mapping):
        raise ValueError("2BGA Stage 3 candidate must be an object")
    claim = dict(candidate)
    code = build_candidate_code(claim)
    parameters = validate_candidate_parameters(claim, code)
    required = parameters["required_distance"]
    threshold_only = artifact.get("threshold_only")
    if not isinstance(threshold_only, bool):
        raise ValueError("2BGA artifact threshold_only must be boolean")
    if artifact.get("required_distance") != required:
        raise ValueError("2BGA artifact required_distance does not replay")
    hx, hz, lx, lz = (
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    problem = derive_twobga_subsystem_problem(
        hx,
        hz,
        ell=int(claim["ell"]),
        m=int(claim["m"]),
        expected_n=int(claim["n"]),
        expected_k=int(claim["k"]),
    )
    if (
        not problem.eligible
        or artifact.get("theorem_eligibility") != problem.report
    ):
        raise ValueError("2BGA theorem eligibility does not replay")
    lower = artifact.get("lower_bound_decisions")
    if not isinstance(lower, list) or len(lower) != 2:
        raise ValueError("2BGA artifact lacks both auxiliary lower decisions")
    by_sector = {
        str(wrapper.get("sector")): wrapper
        for wrapper in lower
        if isinstance(wrapper, Mapping)
    }
    if set(by_sector) != set(TWOBGA_PROOF_SECTORS) or not all(
        _valid_auxiliary_lower(
            by_sector[sector],
            problem,
            sector=sector,
            required_distance=required,
        )
        for sector in TWOBGA_PROOF_SECTORS
    ):
        raise ValueError("2BGA auxiliary lower decisions do not replay")
    original_detector = verify_css_logical_detectors(hx, hz, lx, lz)
    original_symmetry = verify_bb_translation_symmetry(claim)
    anchors = (
        tuple(int(index) for index in original_symmetry["orbit_representatives"])
        if original_symmetry.get("verified") is True else ()
    )
    if (
        original_detector.get("verified") is not True
        or artifact.get("original_logical_detector") != original_detector
        or artifact.get("original_translation_symmetry") != original_symmetry
    ):
        raise ValueError("original-code detector/symmetry report does not replay")
    upper = artifact.get("upper_witness")
    upper_valid = bool(
        isinstance(upper, Mapping)
        and _valid_original_upper(
            upper,
            hz=hz,
            lz=lz,
            required_distance=required,
            anchors=anchors,
        )
    )
    if artifact.get("status") == "EXACT_PROVEN" and not upper_valid:
        raise ValueError("EXACT_PROVEN 2BGA artifact lacks an original witness")
    if artifact.get("status") == "EXACT_PROVEN" and threshold_only:
        raise ValueError("EXACT_PROVEN 2BGA artifact cannot be threshold-only")
    if artifact.get("status") == "THRESHOLD_PROVEN" and upper_valid:
        raise ValueError("THRESHOLD_PROVEN 2BGA artifact contains an exact witness")

    units = artifact.get("units")
    expected_units = 2 + (0 if threshold_only else 1)
    if (
        artifact.get("expected_units") != expected_units
        or not isinstance(units, list)
        or len(units) != expected_units
        or not all(isinstance(unit, Mapping) for unit in units)
    ):
        raise ValueError("2BGA artifact proof-unit plan is inconsistent")
    by_id = {str(unit.get("unit_id")): unit for unit in units}
    if len(by_id) != expected_units or any(
        by_id.get(f"aux-lower-{sector}") != by_sector[sector]
        for sector in TWOBGA_PROOF_SECTORS
    ):
        raise ValueError("2BGA artifact unit list does not bind lower decisions")
    if threshold_only:
        if "original-upper-X" in by_id or upper is not None:
            raise ValueError("threshold-only 2BGA artifact contains an upper unit")
    elif by_id.get("original-upper-X") != upper:
        raise ValueError("2BGA artifact unit list does not bind its upper attempt")
    terminal_units = sum(
        isinstance(unit.get("solver_evidence"), Mapping)
        and unit["solver_evidence"].get("outcome") in SAT_TERMINAL_OUTCOMES
        for unit in units
    )
    if (
        artifact.get("attempted_units") != expected_units
        or artifact.get("terminal_units") != terminal_units
    ):
        raise ValueError("2BGA artifact proof-unit counters are inconsistent")
    return {
        "claim": claim,
        "code": code,
        "hx": hx,
        "hz": hz,
        "lx": lx,
        "lz": lz,
        "problem": problem,
        "required_distance": required,
        "lower_bound_decisions": [by_sector[sector] for sector in TWOBGA_PROOF_SECTORS],
        "upper_witness": dict(upper) if upper_valid else None,
        "original_logical_detector": original_detector,
        "original_translation_symmetry": original_symmetry,
        "original_anchor_indices": anchors,
    }


def claim_from_twobga_artifact(artifact: Mapping[str, Any]) -> dict[str, Any]:
    """Install a typed Stage 4 request after complete theorem replay."""

    context = validate_twobga_stage3_artifact(artifact)
    claim = dict(context["claim"])
    claim[TWOBGA_REQUEST_FIELD] = {
        "schema_version": 1,
        "stage3_artifact": dict(artifact),
        "stage3_artifact_sha256": artifact["artifact_sha256"],
    }
    return claim


def classify_twobga_units(
    units: Mapping[str, Mapping[str, Any]],
    *,
    required_distance: int,
    threshold_only: bool,
) -> str:
    """Classify typed units without promoting an auxiliary counterexample."""

    required = int(required_distance)
    upper = units.get("original-upper-X")
    if isinstance(upper, Mapping):
        evidence = upper.get("solver_evidence")
        if (
            isinstance(evidence, Mapping)
            and upper.get("witness_verified") is True
            and evidence.get("outcome") == "sat"
            and isinstance(evidence.get("objective"), int)
            and not isinstance(evidence.get("objective"), bool)
            and int(evidence["objective"]) < required
        ):
            # This is a witness in the original code, not the auxiliary code.
            return "REJECTED"

    auxiliary_witness = False
    for sector in TWOBGA_PROOF_SECTORS:
        unit = units.get(f"aux-lower-{sector}")
        evidence = (
            unit.get("solver_evidence")
            if isinstance(unit, Mapping)
            else None
        )
        if (
            isinstance(unit, Mapping)
            and unit.get("witness_verified") is True
            and isinstance(evidence, Mapping)
            and _complete_sat(evidence, required - 1)
        ):
            auxiliary_witness = True
            break
    if auxiliary_witness:
        # This terminal SAT result refutes only the auxiliary lower-bound
        # mechanism, never the original code. Replaying the same checkpoint
        # with a larger timeout cannot change that mathematical fact.
        return TWOBGA_BOUND_INSUFFICIENT_STATUS

    lower_complete = all(
        isinstance(units.get(f"aux-lower-{sector}"), Mapping)
        and _complete_unsat(
            units[f"aux-lower-{sector}"].get("solver_evidence", {}),
            required - 1,
        )
        for sector in TWOBGA_PROOF_SECTORS
    )
    if not lower_complete:
        return "UNRESOLVED"
    if threshold_only:
        return "THRESHOLD_PROVEN"
    if not isinstance(upper, Mapping):
        return "UNRESOLVED"
    evidence = upper.get("solver_evidence")
    if not isinstance(evidence, Mapping):
        return "UNRESOLVED"
    if (
        upper.get("witness_verified") is True
        and _complete_sat(evidence, required)
        and evidence.get("objective") == required
    ):
        return "EXACT_PROVEN"
    if _complete_unsat(evidence, required):
        # The original code has no logical through the requested weight. The
        # lower bound is strong enough to survive Stage 3, but this bounded
        # exact lane has no witness establishing equality d=required.
        return TWOBGA_EXACTNESS_GAP_STATUS
    # Timeout/error/partial upper work remains genuinely retryable.
    return "UNRESOLVED"


def _artifact(
    candidate: Mapping[str, Any],
    *,
    theorem_report: Mapping[str, Any],
    units: Mapping[str, Mapping[str, Any]],
    threshold_only: bool,
    started: float,
    original_logical_detector: Mapping[str, Any] | None,
    original_translation_symmetry: Mapping[str, Any] | None,
    termination: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    eligible = theorem_report.get("eligible") is True
    expected = 0 if not eligible else 2 + (0 if threshold_only else 1)
    terminal = sum(
        isinstance(unit.get("solver_evidence"), Mapping)
        and unit["solver_evidence"].get("outcome") in SAT_TERMINAL_OUTCOMES
        for unit in units.values()
    )
    status = (
        "INELIGIBLE"
        if not eligible
        else classify_twobga_units(
            units,
            required_distance=int(candidate["required_distance"]),
            threshold_only=threshold_only,
        )
    )
    lower = [
        dict(units[f"aux-lower-{sector}"])
        for sector in TWOBGA_PROOF_SECTORS
        if f"aux-lower-{sector}" in units
    ]
    upper = units.get("original-upper-X")
    value: dict[str, Any] = {
        "schema_version": TWOBGA_STAGE3_SCHEMA_VERSION,
        "gate": TWOBGA_STAGE3_GATE,
        "backend": TWOBGA_STAGE3_BACKEND,
        "status": status,
        "candidate": dict(candidate),
        "required_distance": int(candidate["required_distance"]),
        "threshold_only": bool(threshold_only),
        "theorem_eligibility": dict(theorem_report),
        "proof_semantics": {
            "lower_bound": (
                "both dressed auxiliary X/Z decisions UNSAT through d-1"
            ),
            "auxiliary_sat_witness": "inconclusive-for-original-code",
            "original_sat_witness": "valid upper bound for original code",
        },
        "expected_units": expected,
        "attempted_units": len(units),
        "terminal_units": terminal,
        "lower_bound_decisions": lower,
        "upper_witness": (
            None if not isinstance(upper, Mapping) else dict(upper)
        ),
        "auxiliary_witnesses": [
            dict(unit)
            for unit in lower
            if unit.get("solver_evidence", {}).get("outcome") == "sat"
        ],
        "units": [dict(units[key]) for key in sorted(units)],
        "original_logical_detector": (
            None
            if original_logical_detector is None
            else dict(original_logical_detector)
        ),
        "original_translation_symmetry": (
            None
            if original_translation_symmetry is None
            else dict(original_translation_symmetry)
        ),
        "elapsed_s": time.monotonic() - started,
    }
    if termination is not None:
        value["termination"] = dict(termination)
    value["artifact_sha256"] = _canonical_sha256(value)
    return value


def screen_twobga_candidate(
    candidate: dict[str, Any],
    *,
    output: Path,
    timeout: float = 120,
    workers: int = 3,
    threshold_only: bool = False,
    resume: bool = True,
    hard_timeout: float | None = None,
    candidate_timeout: float | None = None,
    termination_grace: float = 2.0,
    cardinality_encoding: str = "kmtotalizer",
    solver: str = "auto",
) -> dict[str, Any]:
    """Run a fail-closed 180-bit subsystem lower-bound attempt."""

    started = time.monotonic()
    if isinstance(workers, bool) or not isinstance(workers, int) or workers < 1:
        raise ValueError("workers must be a positive integer")
    unit_timeout = float(timeout if hard_timeout is None else hard_timeout)
    if not math.isfinite(unit_timeout) or unit_timeout <= 0:
        raise ValueError("SAT unit timeout must be positive and finite")
    grace = float(termination_grace)
    if not math.isfinite(grace) or grace < 0:
        raise ValueError("termination_grace must be finite and nonnegative")

    code = build_candidate_code(candidate)
    validate_candidate_parameters(candidate, code)
    hx, hz, lx, lz = (
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    problem = derive_twobga_subsystem_problem(
        hx,
        hz,
        ell=int(candidate["ell"]),
        m=int(candidate["m"]),
        expected_n=int(candidate["n"]),
        expected_k=int(candidate["k"]),
    )
    if not problem.eligible:
        artifact = _artifact(
            candidate,
            theorem_report=problem.report,
            units={},
            threshold_only=threshold_only,
            started=started,
            original_logical_detector=None,
            original_translation_symmetry=None,
        )
        _atomic_write_json(output, artifact)
        return artifact

    original_detector = verify_css_logical_detectors(hx, hz, lx, lz)
    if original_detector.get("verified") is not True:
        raise ValueError("original CSS logical detector replay failed")
    original_symmetry = verify_bb_translation_symmetry(candidate)
    original_anchors = (
        tuple(int(index) for index in original_symmetry["orbit_representatives"])
        if original_symmetry.get("verified") is True else ()
    )

    specifications: list[dict[str, Any]] = []
    for sector in TWOBGA_PROOF_SECTORS:
        checks, detectors, _gauge = problem.sector_matrices(sector)
        symmetry = problem.report["sectors"][sector]["translation_symmetry"]
        specifications.append({
            "unit_id": f"aux-lower-{sector}",
            "domain": "auxiliary-subsystem",
            "phase": "lower",
            "sector": sector,
            "checks": checks,
            "detectors": detectors,
            "max_weight": int(candidate["required_distance"]) - 1,
            "anchors": (0,) if symmetry.get("verified") is True else (),
            "symmetry_sha256": symmetry["report_sha256"],
        })
    if not threshold_only:
        specifications.append({
            "unit_id": "original-upper-X",
            "domain": "original-code",
            "phase": "upper",
            "sector": "X",
            "checks": hz,
            "detectors": lz,
            "max_weight": int(candidate["required_distance"]),
            "anchors": original_anchors,
            "symmetry_sha256": (
                _canonical_sha256(original_symmetry)
                if original_symmetry.get("verified") is True else None
            ),
        })

    if candidate_timeout is None:
        candidate_budget = (
            math.ceil(len(specifications) / min(workers, len(specifications)))
            * unit_timeout
            + grace
            + 1.0
        )
    else:
        candidate_budget = float(candidate_timeout)
        if not math.isfinite(candidate_budget) or candidate_budget <= 0:
            raise ValueError("candidate_timeout must be positive and finite")
    work_deadline = started + max(0.001, candidate_budget - grace)
    digest = str(candidate["canonical_digest"])
    unit_dir = output.parent / "twobga-units" / hashlib.sha256(
        digest.encode(),
    ).hexdigest()
    cancellation = threading.Event()
    units: dict[str, dict[str, Any]] = {}
    termination: dict[str, Any] | None = None

    def write_progress() -> dict[str, Any]:
        artifact = _artifact(
            candidate,
            theorem_report=problem.report,
            units=units,
            threshold_only=threshold_only,
            started=started,
            original_logical_detector=original_detector,
            original_translation_symmetry=original_symmetry,
            termination=termination,
        )
        _atomic_write_json(output, artifact)
        return artifact

    write_progress()

    def solve_one(specification: Mapping[str, Any]) -> tuple[str, dict[str, Any]]:
        remaining = max(0.001, work_deadline - time.monotonic())
        evidence = solve_css_sector_sat(
            specification["checks"],
            specification["detectors"],
            max_weight=int(specification["max_weight"]),
            timeout=min(unit_timeout, remaining),
            workers=1,
            seed=0,
            partition_index=None,
            anchor_indices=tuple(specification["anchors"]),
            sector=str(specification["sector"]),
            cardinality_encoding=cardinality_encoding,
            solver=solver,
            checkpoint_path=unit_dir / f"{specification['unit_id']}.json",
            resume=resume,
            checkpoint_identity={
                "stage3_gate": TWOBGA_STAGE3_GATE,
                "candidate_digest": digest,
                "theorem_report_sha256": problem.report["report_sha256"],
                "original_logical_detector_sha256": original_detector[
                    "report_sha256"
                ],
                "unit_id": specification["unit_id"],
                "domain": specification["domain"],
                "phase": specification["phase"],
                "symmetry_sha256": specification["symmetry_sha256"],
            },
            cancel_event=cancellation,
            termination_grace_s=grace,
        )
        failures = (
            verify_css_threshold_sat_witness(
                evidence,
                specification["checks"],
                specification["detectors"],
            )
            if evidence.get("outcome") == "sat" else []
        )
        wrapper = {
            "unit_id": specification["unit_id"],
            "domain": specification["domain"],
            "phase": specification["phase"],
            "sector": specification["sector"],
            "max_weight": specification["max_weight"],
            "anchor_indices": list(specification["anchors"]),
            "witness_verified": bool(
                evidence.get("outcome") == "sat" and not failures
            ),
            "witness_failures": failures,
            "solver_evidence": evidence,
        }
        return str(specification["unit_id"]), wrapper

    max_workers = min(workers, len(specifications))
    executor = ThreadPoolExecutor(max_workers=max_workers)
    futures = {
        executor.submit(solve_one, specification): specification
        for specification in specifications
    }
    try:
        for future in as_completed(futures):
            if time.monotonic() >= work_deadline:
                cancellation.set()
            try:
                unit_id, wrapper = future.result()
            except Exception as exc:
                specification = futures[future]
                unit_id = str(specification["unit_id"])
                wrapper = {
                    "unit_id": unit_id,
                    "domain": specification["domain"],
                    "phase": specification["phase"],
                    "sector": specification["sector"],
                    "max_weight": specification["max_weight"],
                    "anchor_indices": list(specification["anchors"]),
                    "witness_verified": False,
                    "witness_failures": [],
                    "solver_evidence": {
                        "outcome": "solver_error",
                        "decision_complete": False,
                        "threshold_infeasible": False,
                        "retryable": True,
                        "message": f"{type(exc).__name__}: {exc}",
                    },
                }
            units[unit_id] = wrapper
            write_progress()
    finally:
        cancellation.set()
        executor.shutdown(wait=True, cancel_futures=True)

    if time.monotonic() >= work_deadline and any(
        unit.get("solver_evidence", {}).get("outcome")
        not in SAT_TERMINAL_OUTCOMES
        for unit in units.values()
    ):
        termination = {
            "reason": "candidate_timeout",
            "retryable": True,
            "candidate_timeout_s": candidate_budget,
        }
    return write_progress()


__all__ = [
    "TWOBGA_BOUND_INSUFFICIENT_STATUS",
    "TWOBGA_EXACTNESS_GAP_STATUS",
    "TWOBGA_PROOF_SECTORS",
    "TWOBGA_EXACT_PROOF_TYPE",
    "TWOBGA_REQUEST_FIELD",
    "TWOBGA_STAGE3_BACKEND",
    "TWOBGA_STAGE3_GATE",
    "TWOBGA_STAGE3_SCHEMA_VERSION",
    "classify_twobga_units",
    "claim_from_twobga_artifact",
    "screen_twobga_candidate",
    "validate_twobga_stage3_artifact",
]
